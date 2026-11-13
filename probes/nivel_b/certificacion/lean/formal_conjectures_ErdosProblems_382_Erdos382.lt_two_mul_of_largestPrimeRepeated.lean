import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 382

*References:*
- [erdosproblems.com/382](https://www.erdosproblems.com/382)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
-/

section

open Filter

namespace Erdos382

/-- `LargestPrimeRepeated u v` means that $1 \leq u \leq v$ and the largest prime $p$ dividing
$\prod_{u \leq m \leq v} m$ appears in it with exponent at least $2$, that is $p^2$ divides the
product.

We require $u \geq 1$, since for $u = 0$ the product is $0$ and `Nat.maxPrimeFac 0 = 0`. We also
require $v \geq 2$: the only other pair is $u = v = 1$, where the product is $1$, which has no
prime factor, and the junk value `Nat.maxPrimeFac 1 = 1` would make the condition hold. -/
def LargestPrimeRepeated (u v : ℕ) : Prop :=
  1 ≤ u ∧ u ≤ v ∧ 2 ≤ v ∧
    Nat.maxPrimeFac (∏ m ∈ Finset.Icc u v, m) ^ 2 ∣ ∏ m ∈ Finset.Icc u v, m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v ≤ 2 * u

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v ≤ 2 * u) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v ≤ 2 * u) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v ≤ 2 * u) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v ≤ 2 * u) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v ≤ 2 * u) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v ≤ 2 * u) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v ≤ 2 * u) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v ≤ 2 * u)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v ≤ 2 * u)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v ≤ 2 * u)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v ≤ 2 * u)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v ≤ 2 * u)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v ≤ 2 * u)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v ≤ 2 * u)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v ≤ 2 * u)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v ≤ 2 * u)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v ≤ 2 * u)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v ≤ 2 * u)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v ≤ 2 * u)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v ≤ 2 * u)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v ≤ 2 * u)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v ≤ 2 * u)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v ≤ 2 * u)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v ≤ 2 * u)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v ≤ 2 * u)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v ≤ 2 * u)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v ≤ 2 * u)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v ≤ 2 * u)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v ≤ 2 * u)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v ≤ 2 * u)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v ≤ 2 * u)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v ≤ 2 * u)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v ≤ 2 * u)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v ≤ 2 * u)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v ≤ 2 * u)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v ≤ 2 * u)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v ≤ 2 * u)) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v ≤ 2 * u)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v ≤ 2 * u)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 3 * u

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 3 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 3 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 3 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 3 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 3 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 3 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 3 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 3 * u) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 3 * u) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 3 * u) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 3 * u) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 3 * u) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 3 * u) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 3 * u) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v < 3 * u)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v < 3 * u)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v < 3 * u)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v < 3 * u)) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v < 3 * u)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v < 3 * u)) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v < 3 * u)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v < 3 * u)) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v < 3 * u)) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v < 3 * u)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v < 3 * u)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v < 3 * u)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v < 3 * u)) :=
  ⟨(4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v < 3 * u)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v < 3 * u)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v < 3 * u)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v < 3 * u)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v < 3 * u)) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v < 3 * u)) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v < 3 * u)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v < 3 * u)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v < 3 * u)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v < 3 * u)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v < 3 * u)) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v < 3 * u)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v < 3 * u)) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v < 3 * u)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v < 3 * u)) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v < 3 * u)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v < 3 * u)) :=
  ⟨(4 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v < 3 * u)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v < 3 * u)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v < 3 * u)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v < 3 * u)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v < 3 * u)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v < 3 * u)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v < 3 * u)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v < 3 * u)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v < 3 * u)) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v < 3 * u)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v < 3 * u)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v < 3 * u)) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v < 3 * u)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v < 3 * u)) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v < 3 * u)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v < 3 * u)) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v < 3 * u)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v < 3 * u)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v < 3 * u)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v < 3 * u)) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v < 3 * u)) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v < 3 * u)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v < 3 * u)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v < 3 * u)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v < 3 * u)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v < 3 * u)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v < 3 * u)) :=
  ⟨(4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v < 3 * u)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v < 3 * u)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v < 3 * u)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v < 3 * u)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v < 3 * u)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v < 3 * u)) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v < 3 * u)) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v > 2 * u

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v > 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v > 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v > 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v > 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v > 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v > 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v > 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v > 2 * u) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v > 2 * u) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v > 2 * u) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v > 2 * u) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v > 2 * u) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v > 2 * u) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v > 2 * u) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v > 2 * u)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v > 2 * u)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v > 2 * u)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v > 2 * u)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v > 2 * u)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v > 2 * u)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v > 2 * u)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v > 2 * u)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v > 2 * u)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v > 2 * u)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v > 2 * u)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v > 2 * u)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v > 2 * u)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v > 2 * u)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v > 2 * u)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v > 2 * u)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v > 2 * u)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v > 2 * u)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v > 2 * u)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v > 2 * u)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v > 2 * u)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v > 2 * u)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v > 2 * u)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v > 2 * u)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v > 2 * u)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v > 2 * u)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v > 2 * u)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v > 2 * u)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v > 2 * u)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v > 2 * u)) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v > 2 * u)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(v > 2 * u)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v > 2 * u)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v > 2 * u)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v > 2 * u)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v > 2 * u)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v > 2 * u)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v > 2 * u)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v > 2 * u)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v > 2 * u)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v > 2 * u)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v > 2 * u)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v > 2 * u)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v > 2 * u)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v > 2 * u)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v > 2 * u)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v > 2 * u)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v > 2 * u)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v > 2 * u)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v > 2 * u)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v > 2 * u)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v > 2 * u)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v > 2 * u)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v > 2 * u)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v > 2 * u)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v > 2 * u)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v > 2 * u)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v > 2 * u)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v > 2 * u)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v > 2 * u)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v > 2 * u)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v > 2 * u)) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v > 2 * u)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (v > 2 * u)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {u v : ℕ} (h : LargestPrimeRepeated u v), 2 * u > v

set_option maxHeartbeats 200000 in
example {u v : ℕ} :
    (v < 2 * u) ↔ (2 * u > v) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {u v : ℕ} :
    (v < 2 * u) ↔ (2 * u > v) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {u v : ℕ} :
    (v < 2 * u) ↔ (2 * u > v) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {u v : ℕ} :
    (v < 2 * u) ↔ (2 * u > v) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {u v : ℕ} :
    (v < 2 * u) ↔ (2 * u > v) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {u v : ℕ} :
    (v < 2 * u) ↔ (2 * u > v) := by
  omega

set_option maxHeartbeats 200000 in
example {u v : ℕ} :
    (v < 2 * u) ↔ (2 * u > v) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {u v : ℕ} :
    (v < 2 * u) ↔ (2 * u > v) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) ↔
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), 2 * u > v) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) ↔
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), 2 * u > v) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) ↔
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), 2 * u > v) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) ↔
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), 2 * u > v) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {u v : ℕ} (h₀ : LargestPrimeRepeated u v), v < 2 * u

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) ↔
    (∀ {u v : ℕ} (h₀ : LargestPrimeRepeated u v), v < 2 * u) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) ↔
    (∀ {u v : ℕ} (h₀ : LargestPrimeRepeated u v), v < 2 * u) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) ↔
    (∀ {u v : ℕ} (h₀ : LargestPrimeRepeated u v), v < 2 * u) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) ↔
    (∀ {u v : ℕ} (h₀ : LargestPrimeRepeated u v), v < 2 * u) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {u v : ℕ} (h : LargestPrimeRepeated u v), ¬(2 * u ≤ v)

set_option maxHeartbeats 200000 in
example {u v : ℕ} :
    (v < 2 * u) ↔ (¬(2 * u ≤ v)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {u v : ℕ} :
    (v < 2 * u) ↔ (¬(2 * u ≤ v)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {u v : ℕ} :
    (v < 2 * u) ↔ (¬(2 * u ≤ v)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {u v : ℕ} :
    (v < 2 * u) ↔ (¬(2 * u ≤ v)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {u v : ℕ} :
    (v < 2 * u) ↔ (¬(2 * u ≤ v)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {u v : ℕ} :
    (v < 2 * u) ↔ (¬(2 * u ≤ v)) := by
  omega

set_option maxHeartbeats 200000 in
example {u v : ℕ} :
    (v < 2 * u) ↔ (¬(2 * u ≤ v)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {u v : ℕ} :
    (v < 2 * u) ↔ (¬(2 * u ≤ v)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) ↔
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), ¬(2 * u ≤ v)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) ↔
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), ¬(2 * u ≤ v)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) ↔
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), ¬(2 * u ≤ v)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) ↔
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), ¬(2 * u ≤ v)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {u v : ℕ} (h : LargestPrimeRepeated u v), 2 * u ≥ v

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), 2 * u ≥ v) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), 2 * u ≥ v) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), 2 * u ≥ v) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), 2 * u ≥ v) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), 2 * u ≥ v) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), 2 * u ≥ v) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), 2 * u ≥ v) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u ≥ v)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u ≥ v)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u ≥ v)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u ≥ v)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u ≥ v)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u ≥ v)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u ≥ v)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u ≥ v)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u ≥ v)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u ≥ v)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u ≥ v)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u ≥ v)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u ≥ v)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u ≥ v)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u ≥ v)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u ≥ v)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u ≥ v)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u ≥ v)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u ≥ v)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u ≥ v)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u ≥ v)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u ≥ v)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u ≥ v)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u ≥ v)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u ≥ v)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u ≥ v)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u ≥ v)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u ≥ v)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u ≥ v)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u ≥ v)) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u ≥ v)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u ≥ v)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {u v : ℕ} (h : LargestPrimeRepeated u v), 3 * u > v

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), 3 * u > v) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), 3 * u > v) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), 3 * u > v) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), 3 * u > v) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), 3 * u > v) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), 3 * u > v) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), 3 * u > v) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), 3 * u > v) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), 3 * u > v) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), 3 * u > v) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), 3 * u > v) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), 3 * u > v) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), 3 * u > v) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), 3 * u > v) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(3 * u > v)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(3 * u > v)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(3 * u > v)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(3 * u > v)) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(3 * u > v)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(3 * u > v)) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(3 * u > v)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(3 * u > v)) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(3 * u > v)) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(3 * u > v)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(3 * u > v)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(3 * u > v)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(3 * u > v)) :=
  ⟨(4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(3 * u > v)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(3 * u > v)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(3 * u > v)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(3 * u > v)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(3 * u > v)) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(3 * u > v)) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(3 * u > v)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(3 * u > v)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(3 * u > v)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(3 * u > v)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(3 * u > v)) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(3 * u > v)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(3 * u > v)) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(3 * u > v)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(3 * u > v)) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(3 * u > v)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(3 * u > v)) :=
  ⟨(4 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(3 * u > v)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(3 * u > v)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (3 * u > v)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (3 * u > v)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (3 * u > v)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (3 * u > v)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (3 * u > v)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (3 * u > v)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (3 * u > v)) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (3 * u > v)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (3 * u > v)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (3 * u > v)) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (3 * u > v)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (3 * u > v)) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (3 * u > v)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (3 * u > v)) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (3 * u > v)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (3 * u > v)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (3 * u > v)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (3 * u > v)) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (3 * u > v)) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (3 * u > v)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (3 * u > v)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (3 * u > v)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (3 * u > v)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (3 * u > v)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (3 * u > v)) :=
  ⟨(4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (3 * u > v)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (3 * u > v)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (3 * u > v)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (3 * u > v)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (3 * u > v)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (3 * u > v)) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (3 * u > v)) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {u v : ℕ} (h : LargestPrimeRepeated u v), 2 * u < v

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), 2 * u < v) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), 2 * u < v) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), 2 * u < v) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), 2 * u < v) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), 2 * u < v) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), 2 * u < v) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), 2 * u < v) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), 2 * u < v) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), 2 * u < v) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), 2 * u < v) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), 2 * u < v) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), 2 * u < v) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), 2 * u < v) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), v < 2 * u) →
    (∀ {u v : ℕ} (h : LargestPrimeRepeated u v), 2 * u < v) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(2 * u < v)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(2 * u < v)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(2 * u < v)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(2 * u < v)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(2 * u < v)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(2 * u < v)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(2 * u < v)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(2 * u < v)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(2 * u < v)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(2 * u < v)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(2 * u < v)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(2 * u < v)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(2 * u < v)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(2 * u < v)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(2 * u < v)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(2 * u < v)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(2 * u < v)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(2 * u < v)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(2 * u < v)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(2 * u < v)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(2 * u < v)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(2 * u < v)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(2 * u < v)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(2 * u < v)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(2 * u < v)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(2 * u < v)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(2 * u < v)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(2 * u < v)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(2 * u < v)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(2 * u < v)) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(2 * u < v)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), (LargestPrimeRepeated u v) ∧ (¬(2 * u < v)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u < v)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u < v)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u < v)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u < v)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u < v)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u < v)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u < v)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u < v)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u < v)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u < v)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u < v)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u < v)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u < v)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u < v)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u < v)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u < v)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u < v)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u < v)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u < v)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u < v)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u < v)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u < v)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u < v)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u < v)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u < v)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u < v)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u < v)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u < v)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u < v)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u < v)) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u < v)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ) (v : ℕ), ¬((v < 2 * u) ↔ (2 * u < v)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {u v : ℕ} (h : LargestPrimeRepeated u v) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {u v : ℕ} (h : LargestPrimeRepeated u v) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {u v : ℕ} (h : LargestPrimeRepeated u v) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {u v : ℕ} (h : LargestPrimeRepeated u v) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {u v : ℕ} (h : LargestPrimeRepeated u v) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
