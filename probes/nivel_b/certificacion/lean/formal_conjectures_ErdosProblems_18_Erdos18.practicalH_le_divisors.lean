import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.NumberTheory.AdditivelyComplete
--   import FormalConjecturesForMathlib.NumberTheory.PracticalNumbers
/-!
# Erdős Problem 18

*Reference:*
* [erdosproblems.com/18](https://www.erdosproblems.com/18)
* [ErGr80] Erdős, P. and Graham, R. L. (1980). Old and New Problems and Results in Combinatorial Number
Theory. Monographies de L'Enseignement Mathématique, 28. Université de Genève. (See the
sections on Egyptian fractions or practical numbers).
* [Vo85] Vose, Michael D., Egyptian fractions. Bull. London Math. Soc. (1985), 21-24.
-/

section

open Filter Asymptotics Real

namespace Erdos18

/-- For a practical number $n$, $h(n)$ is the maximum over all $1 ≤ m ≤ n$ of
the minimum number of divisors of $n$ needed to represent $m$ as a sum of
distinct divisors. -/
noncomputable def practicalH (n : ℕ) : ℕ :=
  Finset.sup (Finset.Icc 1 n) fun m =>
    sInf {k | ∃ D : Finset ℕ, D ⊆ n.divisors ∧ D.card = k ∧ m ∈ subsetSums D}

/- ### Examples for `practicalH` -/

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n < n.divisors.card

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n < n.divisors.card) →
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n < n.divisors.card) →
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n < n.divisors.card) →
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n < n.divisors.card) →
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n < n.divisors.card) →
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n < n.divisors.card) →
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n < n.divisors.card) →
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Nat.IsPractical n) ∧ (¬(practicalH n < n.divisors.card)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Nat.IsPractical n) ∧ (¬(practicalH n < n.divisors.card)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Nat.IsPractical n) ∧ (¬(practicalH n < n.divisors.card)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Nat.IsPractical n) ∧ (¬(practicalH n < n.divisors.card)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Nat.IsPractical n) ∧ (¬(practicalH n < n.divisors.card)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Nat.IsPractical n) ∧ (¬(practicalH n < n.divisors.card)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((practicalH n ≤ n.divisors.card) ↔ (practicalH n < n.divisors.card)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((practicalH n ≤ n.divisors.card) ↔ (practicalH n < n.divisors.card)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((practicalH n ≤ n.divisors.card) ↔ (practicalH n < n.divisors.card)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((practicalH n ≤ n.divisors.card) ↔ (practicalH n < n.divisors.card)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((practicalH n ≤ n.divisors.card) ↔ (practicalH n < n.divisors.card)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((practicalH n ≤ n.divisors.card) ↔ (practicalH n < n.divisors.card)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≥ n.divisors.card

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≥ n.divisors.card) →
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≥ n.divisors.card) →
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≥ n.divisors.card) →
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≥ n.divisors.card) →
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≥ n.divisors.card) →
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≥ n.divisors.card) →
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≥ n.divisors.card) →
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) →
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≥ n.divisors.card) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) →
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≥ n.divisors.card) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) →
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≥ n.divisors.card) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) →
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≥ n.divisors.card) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) →
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≥ n.divisors.card) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) →
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≥ n.divisors.card) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) →
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≥ n.divisors.card) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Nat.IsPractical n) ∧ (¬(practicalH n ≥ n.divisors.card)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Nat.IsPractical n) ∧ (¬(practicalH n ≥ n.divisors.card)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Nat.IsPractical n) ∧ (¬(practicalH n ≥ n.divisors.card)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Nat.IsPractical n) ∧ (¬(practicalH n ≥ n.divisors.card)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Nat.IsPractical n) ∧ (¬(practicalH n ≥ n.divisors.card)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Nat.IsPractical n) ∧ (¬(practicalH n ≥ n.divisors.card)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((practicalH n ≤ n.divisors.card) ↔ (practicalH n ≥ n.divisors.card)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((practicalH n ≤ n.divisors.card) ↔ (practicalH n ≥ n.divisors.card)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((practicalH n ≤ n.divisors.card) ↔ (practicalH n ≥ n.divisors.card)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((practicalH n ≤ n.divisors.card) ↔ (practicalH n ≥ n.divisors.card)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((practicalH n ≤ n.divisors.card) ↔ (practicalH n ≥ n.divisors.card)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((practicalH n ≤ n.divisors.card) ↔ (practicalH n ≥ n.divisors.card)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Nat.IsPractical n), n.divisors.card ≥ practicalH n

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (practicalH n ≤ n.divisors.card) ↔ (n.divisors.card ≥ practicalH n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (practicalH n ≤ n.divisors.card) ↔ (n.divisors.card ≥ practicalH n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (practicalH n ≤ n.divisors.card) ↔ (n.divisors.card ≥ practicalH n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (practicalH n ≤ n.divisors.card) ↔ (n.divisors.card ≥ practicalH n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (practicalH n ≤ n.divisors.card) ↔ (n.divisors.card ≥ practicalH n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (practicalH n ≤ n.divisors.card) ↔ (n.divisors.card ≥ practicalH n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (practicalH n ≤ n.divisors.card) ↔ (n.divisors.card ≥ practicalH n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (practicalH n ≤ n.divisors.card) ↔ (n.divisors.card ≥ practicalH n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) ↔
    (∀ (n : ℕ) (hn : Nat.IsPractical n), n.divisors.card ≥ practicalH n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) ↔
    (∀ (n : ℕ) (hn : Nat.IsPractical n), n.divisors.card ≥ practicalH n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) ↔
    (∀ (n : ℕ) (hn : Nat.IsPractical n), n.divisors.card ≥ practicalH n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) ↔
    (∀ (n : ℕ) (hn : Nat.IsPractical n), n.divisors.card ≥ practicalH n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn₀ : Nat.IsPractical n), practicalH n ≤ n.divisors.card

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) ↔
    (∀ (n : ℕ) (hn₀ : Nat.IsPractical n), practicalH n ≤ n.divisors.card) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) ↔
    (∀ (n : ℕ) (hn₀ : Nat.IsPractical n), practicalH n ≤ n.divisors.card) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) ↔
    (∀ (n : ℕ) (hn₀ : Nat.IsPractical n), practicalH n ≤ n.divisors.card) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) ↔
    (∀ (n : ℕ) (hn₀ : Nat.IsPractical n), practicalH n ≤ n.divisors.card) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Nat.IsPractical n), ¬(n.divisors.card < practicalH n)

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (practicalH n ≤ n.divisors.card) ↔ (¬(n.divisors.card < practicalH n)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (practicalH n ≤ n.divisors.card) ↔ (¬(n.divisors.card < practicalH n)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (practicalH n ≤ n.divisors.card) ↔ (¬(n.divisors.card < practicalH n)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (practicalH n ≤ n.divisors.card) ↔ (¬(n.divisors.card < practicalH n)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (practicalH n ≤ n.divisors.card) ↔ (¬(n.divisors.card < practicalH n)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (practicalH n ≤ n.divisors.card) ↔ (¬(n.divisors.card < practicalH n)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (practicalH n ≤ n.divisors.card) ↔ (¬(n.divisors.card < practicalH n)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (practicalH n ≤ n.divisors.card) ↔ (¬(n.divisors.card < practicalH n)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) ↔
    (∀ (n : ℕ) (hn : Nat.IsPractical n), ¬(n.divisors.card < practicalH n)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) ↔
    (∀ (n : ℕ) (hn : Nat.IsPractical n), ¬(n.divisors.card < practicalH n)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) ↔
    (∀ (n : ℕ) (hn : Nat.IsPractical n), ¬(n.divisors.card < practicalH n)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) ↔
    (∀ (n : ℕ) (hn : Nat.IsPractical n), ¬(n.divisors.card < practicalH n)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Nat.IsPractical n), n.divisors.card > practicalH n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), n.divisors.card > practicalH n) →
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), n.divisors.card > practicalH n) →
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), n.divisors.card > practicalH n) →
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), n.divisors.card > practicalH n) →
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), n.divisors.card > practicalH n) →
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), n.divisors.card > practicalH n) →
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), n.divisors.card > practicalH n) →
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Nat.IsPractical n) ∧ (¬(n.divisors.card > practicalH n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Nat.IsPractical n) ∧ (¬(n.divisors.card > practicalH n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Nat.IsPractical n) ∧ (¬(n.divisors.card > practicalH n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Nat.IsPractical n) ∧ (¬(n.divisors.card > practicalH n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Nat.IsPractical n) ∧ (¬(n.divisors.card > practicalH n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Nat.IsPractical n) ∧ (¬(n.divisors.card > practicalH n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((practicalH n ≤ n.divisors.card) ↔ (n.divisors.card > practicalH n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((practicalH n ≤ n.divisors.card) ↔ (n.divisors.card > practicalH n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((practicalH n ≤ n.divisors.card) ↔ (n.divisors.card > practicalH n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((practicalH n ≤ n.divisors.card) ↔ (n.divisors.card > practicalH n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((practicalH n ≤ n.divisors.card) ↔ (n.divisors.card > practicalH n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((practicalH n ≤ n.divisors.card) ↔ (n.divisors.card > practicalH n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Nat.IsPractical n), n.divisors.card ≤ practicalH n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), n.divisors.card ≤ practicalH n) →
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), n.divisors.card ≤ practicalH n) →
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), n.divisors.card ≤ practicalH n) →
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), n.divisors.card ≤ practicalH n) →
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), n.divisors.card ≤ practicalH n) →
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), n.divisors.card ≤ practicalH n) →
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), n.divisors.card ≤ practicalH n) →
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) →
    (∀ (n : ℕ) (hn : Nat.IsPractical n), n.divisors.card ≤ practicalH n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) →
    (∀ (n : ℕ) (hn : Nat.IsPractical n), n.divisors.card ≤ practicalH n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) →
    (∀ (n : ℕ) (hn : Nat.IsPractical n), n.divisors.card ≤ practicalH n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) →
    (∀ (n : ℕ) (hn : Nat.IsPractical n), n.divisors.card ≤ practicalH n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) →
    (∀ (n : ℕ) (hn : Nat.IsPractical n), n.divisors.card ≤ practicalH n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) →
    (∀ (n : ℕ) (hn : Nat.IsPractical n), n.divisors.card ≤ practicalH n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Nat.IsPractical n), practicalH n ≤ n.divisors.card) →
    (∀ (n : ℕ) (hn : Nat.IsPractical n), n.divisors.card ≤ practicalH n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Nat.IsPractical n) ∧ (¬(n.divisors.card ≤ practicalH n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Nat.IsPractical n) ∧ (¬(n.divisors.card ≤ practicalH n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Nat.IsPractical n) ∧ (¬(n.divisors.card ≤ practicalH n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Nat.IsPractical n) ∧ (¬(n.divisors.card ≤ practicalH n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Nat.IsPractical n) ∧ (¬(n.divisors.card ≤ practicalH n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Nat.IsPractical n) ∧ (¬(n.divisors.card ≤ practicalH n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((practicalH n ≤ n.divisors.card) ↔ (n.divisors.card ≤ practicalH n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((practicalH n ≤ n.divisors.card) ↔ (n.divisors.card ≤ practicalH n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((practicalH n ≤ n.divisors.card) ↔ (n.divisors.card ≤ practicalH n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((practicalH n ≤ n.divisors.card) ↔ (n.divisors.card ≤ practicalH n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((practicalH n ≤ n.divisors.card) ↔ (n.divisors.card ≤ practicalH n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((practicalH n ≤ n.divisors.card) ↔ (n.divisors.card ≤ practicalH n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Nat.IsPractical n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Nat.IsPractical n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Nat.IsPractical n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Nat.IsPractical n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Nat.IsPractical n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
