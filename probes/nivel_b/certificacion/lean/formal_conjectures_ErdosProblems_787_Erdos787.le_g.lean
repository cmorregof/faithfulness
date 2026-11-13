import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Combinatorics.Additive.RestrictedSumset
/-!
# Erdős Problem 787

*References:*
- [erdosproblems.com/787](https://www.erdosproblems.com/787)
- [Be25] Beker, A., *The Erdős-Moser sum-free set problem via improved bounds for
  $k$-configurations*. [arXiv:2501.10203](https://arxiv.org/abs/2501.10203) (2025).
- [Ch71] Choi, S. L. G., *On a combinatorial problem in number theory*.
  Proc. London Math. Soc. (3) (1971), 629-642.
- [Er65] Erdős, P., *Extremal problems in number theory*. Proc. Sympos. Pure Math., Vol. VIII
  (1965), 181-189. [PDF](https://www.renyi.hu/~p_erdos/1965-02.pdf)
- [Er73] Erdős, P., *Problems and results on combinatorial number theory*. A survey of
  combinatorial theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins, Colo.,
  1971) (1973), 117-138. [PDF](https://www.renyi.hu/~p_erdos/1973-21.pdf)
- [Ru05] Ruzsa, Imre Z., *Sum-avoiding subsets*. Ramanujan J. (2005), 77-82.
- [Sa21] Sanders, Tom, *The Erdős-Moser sum-free set problem*. Canad. J. Math. (2021), 63-107.
-/

section

open Filter Asymptotics

namespace Erdos787

/--
`g G n` is the largest `m` such that every set `A` of `n` elements of `G` has a subset `B` with
$\lvert B\rvert \geq m$ and $b_1 + b_2 \notin A$ for all distinct $b_1, b_2 \in B$
[Er65, p. 187]. The problem takes `G = ℝ`.

The condition on `B` is `Disjoint B.restrictedSumset A`. For `G = ℝ` or `G = ℤ`, the set of such
`m` contains `0` and is bounded by `n`, so `sSup` is its maximum, not a junk value.
-/
noncomputable def g (G : Type*) [Add G] [DecidableEq G] (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∀ A : Finset G, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m < g ℝ n

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m < g ℝ n) →
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m < g ℝ n) →
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m < g ℝ n) →
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m < g ℝ n) →
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m < g ℝ n) →
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m < g ℝ n) →
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m < g ℝ n) →
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m < g ℝ n)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m < g ℝ n)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m < g ℝ n)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m < g ℝ n)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m < g ℝ n)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m < g ℝ n)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m < g ℝ n)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m < g ℝ n)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m < g ℝ n)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m < g ℝ n)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m < g ℝ n)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m < g ℝ n)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m < g ℝ n)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m < g ℝ n)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m < g ℝ n)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m < g ℝ n)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m < g ℝ n)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m < g ℝ n)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m < g ℝ n)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m < g ℝ n)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m < g ℝ n)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m < g ℝ n)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m < g ℝ n)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m < g ℝ n)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m < g ℝ n)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m < g ℝ n)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m < g ℝ n)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m < g ℝ n)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m < g ℝ n)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m < g ℝ n)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m < g ℝ n)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m < g ℝ n)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m < g ℝ n)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m < g ℝ n)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m < g ℝ n)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m < g ℝ n)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m < g ℝ n)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m < g ℝ n)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m < g ℝ n)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m < g ℝ n)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m < g ℝ n)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m < g ℝ n)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m < g ℝ n)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m < g ℝ n)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m < g ℝ n)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m < g ℝ n)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m < g ℝ n)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m < g ℝ n)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m < g ℝ n)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m < g ℝ n)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m < g ℝ n)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m < g ℝ n)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m < g ℝ n)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m < g ℝ n)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m < g ℝ n)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m < g ℝ n)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m < g ℝ n)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m < g ℝ n)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m < g ℝ n)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m < g ℝ n)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m < g ℝ n)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m < g ℝ n)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m < g ℝ n)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m < g ℝ n)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≥ g ℝ n

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≥ g ℝ n) →
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≥ g ℝ n) →
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≥ g ℝ n) →
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≥ g ℝ n) →
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≥ g ℝ n) →
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≥ g ℝ n) →
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≥ g ℝ n) →
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) →
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≥ g ℝ n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) →
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≥ g ℝ n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) →
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≥ g ℝ n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) →
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≥ g ℝ n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) →
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≥ g ℝ n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) →
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≥ g ℝ n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) →
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≥ g ℝ n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m ≥ g ℝ n)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m ≥ g ℝ n)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m ≥ g ℝ n)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m ≥ g ℝ n)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m ≥ g ℝ n)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m ≥ g ℝ n)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m ≥ g ℝ n)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m ≥ g ℝ n)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m ≥ g ℝ n)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m ≥ g ℝ n)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m ≥ g ℝ n)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m ≥ g ℝ n)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m ≥ g ℝ n)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m ≥ g ℝ n)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m ≥ g ℝ n)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m ≥ g ℝ n)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m ≥ g ℝ n)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m ≥ g ℝ n)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m ≥ g ℝ n)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m ≥ g ℝ n)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m ≥ g ℝ n)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m ≥ g ℝ n)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m ≥ g ℝ n)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m ≥ g ℝ n)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m ≥ g ℝ n)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m ≥ g ℝ n)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m ≥ g ℝ n)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m ≥ g ℝ n)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m ≥ g ℝ n)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m ≥ g ℝ n)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m ≥ g ℝ n)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(m ≥ g ℝ n)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m ≥ g ℝ n)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m ≥ g ℝ n)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m ≥ g ℝ n)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m ≥ g ℝ n)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m ≥ g ℝ n)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m ≥ g ℝ n)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m ≥ g ℝ n)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m ≥ g ℝ n)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m ≥ g ℝ n)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m ≥ g ℝ n)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m ≥ g ℝ n)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m ≥ g ℝ n)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m ≥ g ℝ n)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m ≥ g ℝ n)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m ≥ g ℝ n)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m ≥ g ℝ n)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m ≥ g ℝ n)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m ≥ g ℝ n)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m ≥ g ℝ n)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m ≥ g ℝ n)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m ≥ g ℝ n)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m ≥ g ℝ n)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m ≥ g ℝ n)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m ≥ g ℝ n)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m ≥ g ℝ n)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m ≥ g ℝ n)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m ≥ g ℝ n)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m ≥ g ℝ n)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m ≥ g ℝ n)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m ≥ g ℝ n)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m ≥ g ℝ n)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (m ≥ g ℝ n)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), g ℝ n ≥ m

set_option maxHeartbeats 200000 in
example {n m : ℕ} :
    (m ≤ g ℝ n) ↔ (g ℝ n ≥ m) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n m : ℕ} :
    (m ≤ g ℝ n) ↔ (g ℝ n ≥ m) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n m : ℕ} :
    (m ≤ g ℝ n) ↔ (g ℝ n ≥ m) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n m : ℕ} :
    (m ≤ g ℝ n) ↔ (g ℝ n ≥ m) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n m : ℕ} :
    (m ≤ g ℝ n) ↔ (g ℝ n ≥ m) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n m : ℕ} :
    (m ≤ g ℝ n) ↔ (g ℝ n ≥ m) := by
  omega

set_option maxHeartbeats 200000 in
example {n m : ℕ} :
    (m ≤ g ℝ n) ↔ (g ℝ n ≥ m) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n m : ℕ} :
    (m ≤ g ℝ n) ↔ (g ℝ n ≥ m) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) ↔
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), g ℝ n ≥ m) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) ↔
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), g ℝ n ≥ m) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) ↔
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), g ℝ n ≥ m) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) ↔
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), g ℝ n ≥ m) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n m : ℕ} (h₀ : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) ↔
    (∀ {n m : ℕ} (h₀ : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) ↔
    (∀ {n m : ℕ} (h₀ : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) ↔
    (∀ {n m : ℕ} (h₀ : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) ↔
    (∀ {n m : ℕ} (h₀ : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), ¬(g ℝ n < m)

set_option maxHeartbeats 200000 in
example {n m : ℕ} :
    (m ≤ g ℝ n) ↔ (¬(g ℝ n < m)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n m : ℕ} :
    (m ≤ g ℝ n) ↔ (¬(g ℝ n < m)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n m : ℕ} :
    (m ≤ g ℝ n) ↔ (¬(g ℝ n < m)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n m : ℕ} :
    (m ≤ g ℝ n) ↔ (¬(g ℝ n < m)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n m : ℕ} :
    (m ≤ g ℝ n) ↔ (¬(g ℝ n < m)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n m : ℕ} :
    (m ≤ g ℝ n) ↔ (¬(g ℝ n < m)) := by
  omega

set_option maxHeartbeats 200000 in
example {n m : ℕ} :
    (m ≤ g ℝ n) ↔ (¬(g ℝ n < m)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n m : ℕ} :
    (m ≤ g ℝ n) ↔ (¬(g ℝ n < m)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) ↔
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), ¬(g ℝ n < m)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) ↔
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), ¬(g ℝ n < m)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) ↔
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), ¬(g ℝ n < m)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) ↔
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), ¬(g ℝ n < m)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), g ℝ n > m

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), g ℝ n > m) →
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), g ℝ n > m) →
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), g ℝ n > m) →
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), g ℝ n > m) →
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), g ℝ n > m) →
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), g ℝ n > m) →
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), g ℝ n > m) →
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n > m)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n > m)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n > m)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n > m)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n > m)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n > m)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n > m)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n > m)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n > m)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n > m)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n > m)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n > m)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n > m)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n > m)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n > m)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n > m)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n > m)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n > m)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n > m)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n > m)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n > m)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n > m)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n > m)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n > m)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n > m)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n > m)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n > m)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n > m)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n > m)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n > m)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n > m)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n > m)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n > m)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n > m)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n > m)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n > m)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n > m)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n > m)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n > m)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n > m)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n > m)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n > m)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n > m)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n > m)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n > m)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n > m)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n > m)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n > m)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n > m)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n > m)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n > m)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n > m)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n > m)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n > m)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n > m)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n > m)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n > m)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n > m)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n > m)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n > m)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n > m)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n > m)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n > m)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n > m)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), g ℝ n ≤ m

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), g ℝ n ≤ m) →
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), g ℝ n ≤ m) →
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), g ℝ n ≤ m) →
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), g ℝ n ≤ m) →
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), g ℝ n ≤ m) →
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), g ℝ n ≤ m) →
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), g ℝ n ≤ m) →
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) →
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), g ℝ n ≤ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) →
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), g ℝ n ≤ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) →
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), g ℝ n ≤ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) →
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), g ℝ n ≤ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) →
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), g ℝ n ≤ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) →
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), g ℝ n ≤ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), m ≤ g ℝ n) →
    (∀ {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A), g ℝ n ≤ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n ≤ m)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n ≤ m)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n ≤ m)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n ≤ m)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n ≤ m)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n ≤ m)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n ≤ m)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n ≤ m)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n ≤ m)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n ≤ m)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n ≤ m)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n ≤ m)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n ≤ m)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n ≤ m)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n ≤ m)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n ≤ m)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n ≤ m)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n ≤ m)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n ≤ m)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n ≤ m)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n ≤ m)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n ≤ m)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n ≤ m)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n ≤ m)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n ≤ m)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n ≤ m)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n ≤ m)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n ≤ m)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n ≤ m)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n ≤ m)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n ≤ m)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) ∧ (¬(g ℝ n ≤ m)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n ≤ m)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n ≤ m)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n ≤ m)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n ≤ m)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n ≤ m)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n ≤ m)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n ≤ m)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n ≤ m)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n ≤ m)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n ≤ m)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n ≤ m)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n ≤ m)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n ≤ m)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n ≤ m)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n ≤ m)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n ≤ m)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n ≤ m)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n ≤ m)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n ≤ m)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n ≤ m)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n ≤ m)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n ≤ m)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n ≤ m)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n ≤ m)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n ≤ m)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n ≤ m)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n ≤ m)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n ≤ m)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n ≤ m)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n ≤ m)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n ≤ m)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((m ≤ g ℝ n) ↔ (g ℝ n ≤ m)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
