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
  ∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) < 2 * N

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) < 2 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) < 2 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) < 2 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) < 2 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) < 2 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) < 2 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) < 2 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 3 * N

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 3 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 3 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 3 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 3 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 3 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 3 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 3 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 3 * N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 3 * N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 3 * N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 3 * N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 3 * N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 3 * N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 3 * N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≥ 2 * N

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≥ 2 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≥ 2 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≥ 2 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≥ 2 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≥ 2 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≥ 2 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≥ 2 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≥ 2 * N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≥ 2 * N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≥ 2 * N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≥ 2 * N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≥ 2 * N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≥ 2 * N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≥ 2 * N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), 2 * N ≥ A.card * (A.card - 1)

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (N : ℕ) :
    (A.card * (A.card - 1) ≤ 2 * N) ↔ (2 * N ≥ A.card * (A.card - 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (N : ℕ) :
    (A.card * (A.card - 1) ≤ 2 * N) ↔ (2 * N ≥ A.card * (A.card - 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (N : ℕ) :
    (A.card * (A.card - 1) ≤ 2 * N) ↔ (2 * N ≥ A.card * (A.card - 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (N : ℕ) :
    (A.card * (A.card - 1) ≤ 2 * N) ↔ (2 * N ≥ A.card * (A.card - 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (N : ℕ) :
    (A.card * (A.card - 1) ≤ 2 * N) ↔ (2 * N ≥ A.card * (A.card - 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (N : ℕ) :
    (A.card * (A.card - 1) ≤ 2 * N) ↔ (2 * N ≥ A.card * (A.card - 1)) := by
  omega

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (N : ℕ) :
    (A.card * (A.card - 1) ≤ 2 * N) ↔ (2 * N ≥ A.card * (A.card - 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (N : ℕ) :
    (A.card * (A.card - 1) ≤ 2 * N) ↔ (2 * N ≥ A.card * (A.card - 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) ↔
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), 2 * N ≥ A.card * (A.card - 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) ↔
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), 2 * N ≥ A.card * (A.card - 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) ↔
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), 2 * N ≥ A.card * (A.card - 1)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) ↔
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), 2 * N ≥ A.card * (A.card - 1)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ) (N : ℕ) (hA : A ⊆ Finset.range (N + 1)) (hS : IsSidon (A : Set ℕ)), A.card * (A.card - 1) ≤ 2 * N

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) ↔
    (∀ (A : Finset ℕ) (N : ℕ) (hA : A ⊆ Finset.range (N + 1)) (hS : IsSidon (A : Set ℕ)), A.card * (A.card - 1) ≤ 2 * N) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) ↔
    (∀ (A : Finset ℕ) (N : ℕ) (hA : A ⊆ Finset.range (N + 1)) (hS : IsSidon (A : Set ℕ)), A.card * (A.card - 1) ≤ 2 * N) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) ↔
    (∀ (A : Finset ℕ) (N : ℕ) (hA : A ⊆ Finset.range (N + 1)) (hS : IsSidon (A : Set ℕ)), A.card * (A.card - 1) ≤ 2 * N) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) ↔
    (∀ (A : Finset ℕ) (N : ℕ) (hA : A ⊆ Finset.range (N + 1)) (hS : IsSidon (A : Set ℕ)), A.card * (A.card - 1) ≤ 2 * N) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ) (N : ℕ) (hS₀ : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) ↔
    (∀ (A : Finset ℕ) (N : ℕ) (hS₀ : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) ↔
    (∀ (A : Finset ℕ) (N : ℕ) (hS₀ : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) ↔
    (∀ (A : Finset ℕ) (N : ℕ) (hS₀ : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) ↔
    (∀ (A : Finset ℕ) (N : ℕ) (hS₀ : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), 2 * N > A.card * (A.card - 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), 2 * N > A.card * (A.card - 1)) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), 2 * N > A.card * (A.card - 1)) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), 2 * N > A.card * (A.card - 1)) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), 2 * N > A.card * (A.card - 1)) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), 2 * N > A.card * (A.card - 1)) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), 2 * N > A.card * (A.card - 1)) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), 2 * N > A.card * (A.card - 1)) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), 3 * N ≥ A.card * (A.card - 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), 3 * N ≥ A.card * (A.card - 1)) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), 3 * N ≥ A.card * (A.card - 1)) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), 3 * N ≥ A.card * (A.card - 1)) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), 3 * N ≥ A.card * (A.card - 1)) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), 3 * N ≥ A.card * (A.card - 1)) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), 3 * N ≥ A.card * (A.card - 1)) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), 3 * N ≥ A.card * (A.card - 1)) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), 3 * N ≥ A.card * (A.card - 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), 3 * N ≥ A.card * (A.card - 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), 3 * N ≥ A.card * (A.card - 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), 3 * N ≥ A.card * (A.card - 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), 3 * N ≥ A.card * (A.card - 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), 3 * N ≥ A.card * (A.card - 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), 3 * N ≥ A.card * (A.card - 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), 2 * N ≤ A.card * (A.card - 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), 2 * N ≤ A.card * (A.card - 1)) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), 2 * N ≤ A.card * (A.card - 1)) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), 2 * N ≤ A.card * (A.card - 1)) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), 2 * N ≤ A.card * (A.card - 1)) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), 2 * N ≤ A.card * (A.card - 1)) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), 2 * N ≤ A.card * (A.card - 1)) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), 2 * N ≤ A.card * (A.card - 1)) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), 2 * N ≤ A.card * (A.card - 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), 2 * N ≤ A.card * (A.card - 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), 2 * N ≤ A.card * (A.card - 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), 2 * N ≤ A.card * (A.card - 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), 2 * N ≤ A.card * (A.card - 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), 2 * N ≤ A.card * (A.card - 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), A.card * (A.card - 1) ≤ 2 * N) →
    (∀ (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)), 2 * N ≤ A.card * (A.card - 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (N : ℕ) (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
