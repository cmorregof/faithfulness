import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Data.Set.Density
/-!
# Erdős Problem 10

*References:*
- [erdosproblems.com/10](https://www.erdosproblems.com/10)
- [Cr71] Crocker, R., On the sum of a prime and of two powers of two. Pacific J. Math. 36 (1971),
  103-107.
- [Ga75] Gallagher, P. X., Primes and powers of 2. Acta Arith. 29 (1976), 353-370.
- [GrSo98] Granville, A. and Soundararajan, K., A binary additive problem of Erdős and the
  order of $2$ mod $p^2$. Ramanujan J. 2 (1998), 283-298.
-/

section

open Filter

namespace Erdos10

/--
The set of natural numbers that can be written as a sum
of a prime and at most $k$ powers of $2$.
-/
abbrev sumPrimeAndTwoPows (k : ℕ) : Set ℕ :=
  { p + (pows.map (2 ^ ·)).sum | (p : ℕ) (pows : Multiset ℕ) (_ : p.Prime)
    (_ : pows.card ≤ k)}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε < (sumPrimeAndTwoPows k).lowerDensity

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε < (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε < (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε < (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε < (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε < (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε < (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε < (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ k, 1 - ε < (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ k, 1 - ε < (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ k, 1 - ε < (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ k, 1 - ε < (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ k, 1 - ε < (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ k, 1 - ε < (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔ (∃ k, 1 - ε < (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔ (∃ k, 1 - ε < (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔ (∃ k, 1 - ε < (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔ (∃ k, 1 - ε < (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔ (∃ k, 1 - ε < (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔ (∃ k, 1 - ε < (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 ≤ ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 ≤ ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 ≤ ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 ≤ ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 ≤ ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 ≤ ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 ≤ ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 ≤ ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (ε : ℝ)  :
    (0 < ε) ↔ (0 ≤ ε) := by
  omega

set_option maxHeartbeats 200000 in
example (ε : ℝ)  :
    (0 < ε) ↔ (0 ≤ ε) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (ε : ℝ)  :
    (0 < ε) ↔ (0 ≤ ε) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (ε : ℝ)  :
    (0 < ε) ↔ (0 ≤ ε) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (ε : ℝ)  :
    (0 < ε) ↔ (0 ≤ ε) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (ε : ℝ)  :
    (0 < ε) ↔ (0 ≤ ε) := by
  simp_all

set_option maxHeartbeats 200000 in
example (ε : ℝ)  :
    (0 < ε) ↔ (0 ≤ ε) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (0 ≤ ε)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (0 ≤ ε)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (0 ≤ ε)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (0 ≤ ε)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (0 ≤ ε)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (0 ≤ ε)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔ (∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔ (∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔ (∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔ (∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔ (∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔ (∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : ε > 0), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔
    (∀ (ε : ℝ) (hε : ε > 0), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔
    (∀ (ε : ℝ) (hε : ε > 0), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔
    (∀ (ε : ℝ) (hε : ε > 0), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔
    (∀ (ε : ℝ) (hε : ε > 0), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε), ∃ k₁, 1 - ε ≤ (sumPrimeAndTwoPows k₁).lowerDensity

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔ (∃ k₁, 1 - ε ≤ (sumPrimeAndTwoPows k₁).lowerDensity) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔ (∃ k₁, 1 - ε ≤ (sumPrimeAndTwoPows k₁).lowerDensity) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔ (∃ k₁, 1 - ε ≤ (sumPrimeAndTwoPows k₁).lowerDensity) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔ (∃ k₁, 1 - ε ≤ (sumPrimeAndTwoPows k₁).lowerDensity) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔ (∃ k₁, 1 - ε ≤ (sumPrimeAndTwoPows k₁).lowerDensity) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔ (∃ k₁, 1 - ε ≤ (sumPrimeAndTwoPows k₁).lowerDensity) := by
  omega

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔ (∃ k₁, 1 - ε ≤ (sumPrimeAndTwoPows k₁).lowerDensity) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔ (∃ k₁, 1 - ε ≤ (sumPrimeAndTwoPows k₁).lowerDensity) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k₁, 1 - ε ≤ (sumPrimeAndTwoPows k₁).lowerDensity) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k₁, 1 - ε ≤ (sumPrimeAndTwoPows k₁).lowerDensity) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k₁, 1 - ε ≤ (sumPrimeAndTwoPows k₁).lowerDensity) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k₁, 1 - ε ≤ (sumPrimeAndTwoPows k₁).lowerDensity) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε₀ : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔
    (∀ (ε : ℝ) (hε₀ : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔
    (∀ (ε : ℝ) (hε₀ : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔
    (∀ (ε : ℝ) (hε₀ : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔
    (∀ (ε : ℝ) (hε₀ : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : ¬(ε ≤ 0)), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔
    (∀ (ε : ℝ) (hε : ¬(ε ≤ 0)), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔
    (∀ (ε : ℝ) (hε : ¬(ε ≤ 0)), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔
    (∀ (ε : ℝ) (hε : ¬(ε ≤ 0)), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔
    (∀ (ε : ℝ) (hε : ¬(ε ≤ 0)), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : ε > 0), ∃ k, 1 - ε < (sumPrimeAndTwoPows k).lowerDensity

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε > 0), ∃ k, 1 - ε < (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε > 0), ∃ k, 1 - ε < (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε > 0), ∃ k, 1 - ε < (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε > 0), ∃ k, 1 - ε < (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε > 0), ∃ k, 1 - ε < (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε > 0), ∃ k, 1 - ε < (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε > 0), ∃ k, 1 - ε < (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ k, 1 - ε < (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ k, 1 - ε < (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ k, 1 - ε < (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ k, 1 - ε < (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ k, 1 - ε < (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ k, 1 - ε < (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔ (∃ k, 1 - ε < (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔ (∃ k, 1 - ε < (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔ (∃ k, 1 - ε < (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔ (∃ k, 1 - ε < (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔ (∃ k, 1 - ε < (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔ (∃ k, 1 - ε < (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : ε ≥ 0), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε ≥ 0), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε ≥ 0), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε ≥ 0), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε ≥ 0), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε ≥ 0), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε ≥ 0), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε ≥ 0), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (ε : ℝ)  :
    (0 < ε) ↔ (ε ≥ 0) := by
  omega

set_option maxHeartbeats 200000 in
example (ε : ℝ)  :
    (0 < ε) ↔ (ε ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (ε : ℝ)  :
    (0 < ε) ↔ (ε ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (ε : ℝ)  :
    (0 < ε) ↔ (ε ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (ε : ℝ)  :
    (0 < ε) ↔ (ε ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (ε : ℝ)  :
    (0 < ε) ↔ (ε ≥ 0) := by
  simp_all

set_option maxHeartbeats 200000 in
example (ε : ℝ)  :
    (0 < ε) ↔ (ε ≥ 0) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (ε ≥ 0)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (ε ≥ 0)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (ε ≥ 0)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (ε ≥ 0)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (ε ≥ 0)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (ε ≥ 0)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : ε > 0), ∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε > 0), ∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε > 0), ∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε > 0), ∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε > 0), ∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε > 0), ∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε > 0), ∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε > 0), ∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : ε > 0), ∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : ε > 0), ∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : ε > 0), ∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : ε > 0), ∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : ε > 0), ∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : ε > 0), ∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) →
    (∀ (ε : ℝ) (hε : ε > 0), ∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔ (∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔ (∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔ (∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔ (∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔ (∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity) ↔ (∃ k, 1 - ε ≥ (sumPrimeAndTwoPows k).lowerDensity)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (ε : ℝ) (hε : 0 < ε) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (ε : ℝ) (hε : 0 < ε) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (ε : ℝ) (hε : 0 < ε) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (ε : ℝ) (hε : 0 < ε) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (ε : ℝ) (hε : 0 < ε) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
