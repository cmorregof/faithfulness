import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Combinatorics.Basic
/-!
# Erdős Problem 30

*References:*
- [erdosproblems.com/30](https://www.erdosproblems.com/30)
- [ErTu41] Erdős, P. and Turán, P., *On a problem of Sidon in additive number theory, and on
  some related problems*. J. London Math. Soc. 16 (1941), 212-215.
- [Li69] Lindström, B., *An inequality for $B_2$-sequences*. J. Combinatorial Theory 6 (1969),
  211-212.
- [Si38] Singer, J., *A theorem in finite projective geometry and some applications to number
  theory*. Trans. Amer. Math. Soc. 43 (1938), 377-385.
- [BFR23] Balogh, J., Füredi, Z. and Roy, S., *An upper bound on the size of Sidon sets*.
  Amer. Math. Monthly 130 (2023), 437-445.
- [OB22] O'Bryant, K., *On the size of finite Sidon sets*.
  [arXiv:2207.07800](https://arxiv.org/abs/2207.07800) (2022).
- [CHO25] Carter, D., Hunter, Z. and O'Bryant, K., *On the diameter of finite Sidon sets*.
  Acta Math. Hungar. 175 (2025), 108-126.

See also [Ben Green's Open Problem 31](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf)
(formalised in `FormalConjectures/GreensOpenProblems/31.lean`).
-/

section

namespace Erdos30

/--
Let $h(N)$ be the maximum size of a Sidon set in $\{1, \dots, N\}$.
-/
noncomputable abbrev h (N : ℕ) : ℕ := Finset.maxSidonSubsetCard (Finset.Icc 1 N)

open Filter
open scoped Asymptotics Pointwise

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ), (h N : ℝ) < (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) < (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) < (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) < (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) < (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) < (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) < (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) < (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((h N : ℝ) < (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((h N : ℝ) < (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((h N : ℝ) < (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((h N : ℝ) < (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((h N : ℝ) < (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((h N : ℝ) < (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((h N : ℝ) < (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((h N : ℝ) < (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((h N : ℝ) < (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((h N : ℝ) < (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((h N : ℝ) < (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((h N : ℝ) < (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((h N : ℝ) < (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((h N : ℝ) < (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ), (h N : ℝ) ≥ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≥ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≥ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≥ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≥ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≥ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≥ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≥ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (h N : ℝ) ≥ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (h N : ℝ) ≥ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (h N : ℝ) ≥ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (h N : ℝ) ≥ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (h N : ℝ) ≥ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (h N : ℝ) ≥ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (h N : ℝ) ≥ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((h N : ℝ) ≥ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((h N : ℝ) ≥ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((h N : ℝ) ≥ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((h N : ℝ) ≥ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((h N : ℝ) ≥ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((h N : ℝ) ≥ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((h N : ℝ) ≥ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((h N : ℝ) ≥ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((h N : ℝ) ≥ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((h N : ℝ) ≥ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((h N : ℝ) ≥ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((h N : ℝ) ≥ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((h N : ℝ) ≥ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((h N : ℝ) ≥ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ), (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 ≥ (h N : ℝ)

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    ((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 ≥ (h N : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    ((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 ≥ (h N : ℝ)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    ((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 ≥ (h N : ℝ)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    ((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 ≥ (h N : ℝ)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    ((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 ≥ (h N : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    ((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 ≥ (h N : ℝ)) := by
  omega

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    ((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 ≥ (h N : ℝ)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    ((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 ≥ (h N : ℝ)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔
    (∀ (N : ℕ), (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 ≥ (h N : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔
    (∀ (N : ℕ), (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 ≥ (h N : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔
    (∀ (N : ℕ), (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 ≥ (h N : ℝ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔
    (∀ (N : ℕ), (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 ≥ (h N : ℝ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ), ¬((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 < (h N : ℝ))

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    ((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ (¬((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 < (h N : ℝ))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    ((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ (¬((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 < (h N : ℝ))) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    ((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ (¬((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 < (h N : ℝ))) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    ((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ (¬((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 < (h N : ℝ))) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    ((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ (¬((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 < (h N : ℝ))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    ((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ (¬((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 < (h N : ℝ))) := by
  omega

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    ((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ (¬((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 < (h N : ℝ))) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    ((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ (¬((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 < (h N : ℝ))) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔
    (∀ (N : ℕ), ¬((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 < (h N : ℝ))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔
    (∀ (N : ℕ), ¬((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 < (h N : ℝ))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔
    (∀ (N : ℕ), ¬((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 < (h N : ℝ))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔
    (∀ (N : ℕ), ¬((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 < (h N : ℝ))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ), (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 > (h N : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 > (h N : ℝ)) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 > (h N : ℝ)) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 > (h N : ℝ)) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 > (h N : ℝ)) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 > (h N : ℝ)) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 > (h N : ℝ)) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 > (h N : ℝ)) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 > (h N : ℝ))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 > (h N : ℝ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 > (h N : ℝ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 > (h N : ℝ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 > (h N : ℝ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 > (h N : ℝ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 > (h N : ℝ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 > (h N : ℝ))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 > (h N : ℝ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 > (h N : ℝ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 > (h N : ℝ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 > (h N : ℝ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 > (h N : ℝ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 > (h N : ℝ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ), (N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1 ≥ (h N : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1 ≥ (h N : ℝ)) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1 ≥ (h N : ℝ)) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1 ≥ (h N : ℝ)) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1 ≥ (h N : ℝ)) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1 ≥ (h N : ℝ)) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1 ≥ (h N : ℝ)) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1 ≥ (h N : ℝ)) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1 ≥ (h N : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1 ≥ (h N : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1 ≥ (h N : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1 ≥ (h N : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1 ≥ (h N : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1 ≥ (h N : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1 ≥ (h N : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1 ≥ (h N : ℝ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1 ≥ (h N : ℝ))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1 ≥ (h N : ℝ))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1 ≥ (h N : ℝ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1 ≥ (h N : ℝ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1 ≥ (h N : ℝ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1 ≥ (h N : ℝ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1 ≥ (h N : ℝ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1 ≥ (h N : ℝ))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1 ≥ (h N : ℝ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1 ≥ (h N : ℝ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1 ≥ (h N : ℝ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1 ≥ (h N : ℝ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1 ≥ (h N : ℝ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1 ≥ (h N : ℝ))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((N : ℝ).sqrt + (N : ℝ) ^ (5⁻¹ : ℝ) + 1 ≥ (h N : ℝ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ), (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 ≤ (h N : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 ≤ (h N : ℝ)) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 ≤ (h N : ℝ)) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 ≤ (h N : ℝ)) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 ≤ (h N : ℝ)) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 ≤ (h N : ℝ)) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 ≤ (h N : ℝ)) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 ≤ (h N : ℝ)) →
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 ≤ (h N : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 ≤ (h N : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 ≤ (h N : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 ≤ (h N : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 ≤ (h N : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 ≤ (h N : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ), (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) →
    (∀ (N : ℕ), (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 ≤ (h N : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 ≤ (h N : ℝ))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 ≤ (h N : ℝ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 ≤ (h N : ℝ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 ≤ (h N : ℝ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 ≤ (h N : ℝ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 ≤ (h N : ℝ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 ≤ (h N : ℝ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 ≤ (h N : ℝ))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 ≤ (h N : ℝ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 ≤ (h N : ℝ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 ≤ (h N : ℝ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 ≤ (h N : ℝ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 ≤ (h N : ℝ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬(((h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) ↔ ((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 ≤ (h N : ℝ))) :=
  ⟨(10 : ℕ), by norm_num⟩

#eval "FIN_CERTIFICAR"
