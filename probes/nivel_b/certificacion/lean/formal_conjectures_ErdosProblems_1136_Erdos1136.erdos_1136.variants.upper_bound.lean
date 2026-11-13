import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Data.Set.Density
/-!
# Erdős Problem 1136

*References:*
- [erdosproblems.com/1136](https://www.erdosproblems.com/1136)
- [Mu11] Müller, Helmut, *Über ein additiv-zahlentheoretisches Problem von P. Erdős*.
  Mitt. Math. Ges. Hamburg (2011), 75-78.
-/

section

namespace Erdos1136

/--
A set `A` of natural numbers has the property in the question if `a + b ≠ 2 ^ k` for all
`a, b ∈ A` (not necessarily distinct) and all `k ≥ 0`.
-/
def AvoidsPowersOfTwo (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ k : ℕ, a + b ≠ 2 ^ k

/-- The set of all integers congruent to $3\cdot 2^i\pmod{2^{i+2}}$ for some $i\geq 0$. -/
def muellerSet : Set ℕ := {n | ∃ i : ℕ, n ≡ 3 * 2 ^ i [MOD 2 ^ (i + 2)]}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity < 1 / 2

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity < 1 / 2) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity < 1 / 2) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity < 1 / 2) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity < 1 / 2) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity < 1 / 2) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity < 1 / 2) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity < 1 / 2) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 3

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 3) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 3) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 3) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 3) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 3) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 3) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 3) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≥ 1 / 2

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≥ 1 / 2) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≥ 1 / 2) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≥ 1 / 2) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≥ 1 / 2) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≥ 1 / 2) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≥ 1 / 2) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≥ 1 / 2) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≥ 1 / 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≥ 1 / 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≥ 1 / 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≥ 1 / 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≥ 1 / 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≥ 1 / 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≥ 1 / 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), 1 / 2 ≥ A.lowerDensity

set_option maxHeartbeats 200000 in
example (A : Set ℕ) :
    (A.lowerDensity ≤ 1 / 2) ↔ (1 / 2 ≥ A.lowerDensity) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (A : Set ℕ) :
    (A.lowerDensity ≤ 1 / 2) ↔ (1 / 2 ≥ A.lowerDensity) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (A : Set ℕ) :
    (A.lowerDensity ≤ 1 / 2) ↔ (1 / 2 ≥ A.lowerDensity) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (A : Set ℕ) :
    (A.lowerDensity ≤ 1 / 2) ↔ (1 / 2 ≥ A.lowerDensity) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (A : Set ℕ) :
    (A.lowerDensity ≤ 1 / 2) ↔ (1 / 2 ≥ A.lowerDensity) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (A : Set ℕ) :
    (A.lowerDensity ≤ 1 / 2) ↔ (1 / 2 ≥ A.lowerDensity) := by
  omega

set_option maxHeartbeats 200000 in
example (A : Set ℕ) :
    (A.lowerDensity ≤ 1 / 2) ↔ (1 / 2 ≥ A.lowerDensity) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (A : Set ℕ) :
    (A.lowerDensity ≤ 1 / 2) ↔ (1 / 2 ≥ A.lowerDensity) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) ↔
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), 1 / 2 ≥ A.lowerDensity) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) ↔
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), 1 / 2 ≥ A.lowerDensity) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) ↔
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), 1 / 2 ≥ A.lowerDensity) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) ↔
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), 1 / 2 ≥ A.lowerDensity) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Set ℕ) (hA₀ : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) ↔
    (∀ (A : Set ℕ) (hA₀ : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) ↔
    (∀ (A : Set ℕ) (hA₀ : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) ↔
    (∀ (A : Set ℕ) (hA₀ : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) ↔
    (∀ (A : Set ℕ) (hA₀ : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), 1 / 2 > A.lowerDensity

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), 1 / 2 > A.lowerDensity) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), 1 / 2 > A.lowerDensity) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), 1 / 2 > A.lowerDensity) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), 1 / 2 > A.lowerDensity) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), 1 / 2 > A.lowerDensity) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), 1 / 2 > A.lowerDensity) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), 1 / 2 > A.lowerDensity) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), 1 / 3 ≥ A.lowerDensity

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), 1 / 3 ≥ A.lowerDensity) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), 1 / 3 ≥ A.lowerDensity) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), 1 / 3 ≥ A.lowerDensity) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), 1 / 3 ≥ A.lowerDensity) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), 1 / 3 ≥ A.lowerDensity) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), 1 / 3 ≥ A.lowerDensity) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), 1 / 3 ≥ A.lowerDensity) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), 1 / 3 ≥ A.lowerDensity) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), 1 / 3 ≥ A.lowerDensity) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), 1 / 3 ≥ A.lowerDensity) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), 1 / 3 ≥ A.lowerDensity) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), 1 / 3 ≥ A.lowerDensity) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), 1 / 3 ≥ A.lowerDensity) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), 1 / 3 ≥ A.lowerDensity) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), 1 / 2 ≤ A.lowerDensity

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), 1 / 2 ≤ A.lowerDensity) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), 1 / 2 ≤ A.lowerDensity) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), 1 / 2 ≤ A.lowerDensity) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), 1 / 2 ≤ A.lowerDensity) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), 1 / 2 ≤ A.lowerDensity) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), 1 / 2 ≤ A.lowerDensity) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), 1 / 2 ≤ A.lowerDensity) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), 1 / 2 ≤ A.lowerDensity) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), 1 / 2 ≤ A.lowerDensity) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), 1 / 2 ≤ A.lowerDensity) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), 1 / 2 ≤ A.lowerDensity) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), 1 / 2 ≤ A.lowerDensity) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), 1 / 2 ≤ A.lowerDensity) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), A.lowerDensity ≤ 1 / 2) →
    (∀ (A : Set ℕ) (hA : AvoidsPowersOfTwo A), 1 / 2 ≤ A.lowerDensity) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (A : Set ℕ) (hA : AvoidsPowersOfTwo A) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (A : Set ℕ) (hA : AvoidsPowersOfTwo A) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (A : Set ℕ) (hA : AvoidsPowersOfTwo A) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (A : Set ℕ) (hA : AvoidsPowersOfTwo A) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (A : Set ℕ) (hA : AvoidsPowersOfTwo A) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
