import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 21

*References:*
- [erdosproblems.com/21](https://www.erdosproblems.com/21)
- [Er81] Erdős, P., *On the combinatorial problems which I would most like to see solved*.
  Combinatorica (1981), 25-42.
- [Er90] Erdős, Paul, *Some of my favourite unsolved problems*. A tribute to Paul Erdős (1990),
  467-478.
- [Er92b] Erdős, Paul, *Some of my favourite problems in various branches of combinatorics*.
  Matematiche (Catania) (1992), 231-240.
- [Er97f] Erdős, Paul, *Some unsolved problems*. Combinatorics, geometry and probability
  (Cambridge, 1993) (1997), 1-10.
- [ErLo75] Erdős, P. and Lovász, L., *Problems and results on $3$-chromatic hypergraphs and some
  related questions*. (1975), 609--627.
- [Ka92b] Kahn, Jeff, *On a problem of Erdős and Lovász: random lines in a projective plane*.
  Combinatorica (1992), 417-423.
- [Ka94] Kahn, Jeff, *On a problem of Erdős and Lovász. II. $n(r)=O(r)$*. J. Amer. Math. Soc.
  (1994), 125-143.
- [Tr14] A. Tripathi, *A result on intersecting families with maximum transversal size*.
  arXiv:1409.4610 (2014).
- [BaWa21] J. Barát and I. M. Wanless, *Intersecting and 2-intersecting hypergraphs with maximal
  covering number: the Erdős-Lovász theme revisited*. J. Combin. Des. (2021), 260-286.
-/

section

open Filter

namespace Erdos21

/-- An Erdős–Lovász family of order `n`: an intersecting family of `n`-sets such that every set
of size at most `n - 1` is disjoint from some member. -/
def IsErdosLovaszFamily (n : ℕ) (F : Finset (Finset ℕ)) : Prop :=
  (∀ A ∈ F, A.card = n) ∧ (∀ A ∈ F, ∀ B ∈ F, (A ∩ B).Nonempty) ∧
    ∀ S : Finset ℕ, S.card ≤ n - 1 → ∃ A ∈ F, Disjoint S A

/-- `f n` is the minimal size of an Erdős–Lovász family of order `n`. -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ F : Finset (Finset ℕ), IsErdosLovaszFamily n F ∧ F.card = m}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 < f n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 < f n) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 < f n) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 < f n) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 < f n) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 < f n) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 < f n) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 < f n) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((8 / 3 : ℝ) * n - 3 < f n)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((8 / 3 : ℝ) * n - 3 < f n)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((8 / 3 : ℝ) * n - 3 < f n)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((8 / 3 : ℝ) * n - 3 < f n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((8 / 3 : ℝ) * n - 3 < f n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((8 / 3 : ℝ) * n - 3 < f n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((8 / 3 : ℝ) * n - 3 < f n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((8 / 3 : ℝ) * n - 3 < f n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((8 / 3 : ℝ) * n - 3 < f n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((8 / 3 : ℝ) * n - 3 < f n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ ((8 / 3 : ℝ) * n - 3 < f n)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ ((8 / 3 : ℝ) * n - 3 < f n)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ ((8 / 3 : ℝ) * n - 3 < f n)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ ((8 / 3 : ℝ) * n - 3 < f n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ ((8 / 3 : ℝ) * n - 3 < f n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ ((8 / 3 : ℝ) * n - 3 < f n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ ((8 / 3 : ℝ) * n - 3 < f n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ ((8 / 3 : ℝ) * n - 3 < f n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ ((8 / 3 : ℝ) * n - 3 < f n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ ((8 / 3 : ℝ) * n - 3 < f n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), (9 / 3 : ℝ) * n - 3 ≤ f n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (9 / 3 : ℝ) * n - 3 ≤ f n) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (9 / 3 : ℝ) * n - 3 ≤ f n) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (9 / 3 : ℝ) * n - 3 ≤ f n) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (9 / 3 : ℝ) * n - 3 ≤ f n) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (9 / 3 : ℝ) * n - 3 ≤ f n) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (9 / 3 : ℝ) * n - 3 ≤ f n) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (9 / 3 : ℝ) * n - 3 ≤ f n) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) →
    (∀ (n : ℕ), (9 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) →
    (∀ (n : ℕ), (9 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) →
    (∀ (n : ℕ), (9 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) →
    (∀ (n : ℕ), (9 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) →
    (∀ (n : ℕ), (9 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) →
    (∀ (n : ℕ), (9 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) →
    (∀ (n : ℕ), (9 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((9 / 3 : ℝ) * n - 3 ≤ f n)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((9 / 3 : ℝ) * n - 3 ≤ f n)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((9 / 3 : ℝ) * n - 3 ≤ f n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((9 / 3 : ℝ) * n - 3 ≤ f n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((9 / 3 : ℝ) * n - 3 ≤ f n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((9 / 3 : ℝ) * n - 3 ≤ f n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((9 / 3 : ℝ) * n - 3 ≤ f n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((9 / 3 : ℝ) * n - 3 ≤ f n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((9 / 3 : ℝ) * n - 3 ≤ f n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ ((9 / 3 : ℝ) * n - 3 ≤ f n)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ ((9 / 3 : ℝ) * n - 3 ≤ f n)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ ((9 / 3 : ℝ) * n - 3 ≤ f n)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ ((9 / 3 : ℝ) * n - 3 ≤ f n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ ((9 / 3 : ℝ) * n - 3 ≤ f n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ ((9 / 3 : ℝ) * n - 3 ≤ f n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ ((9 / 3 : ℝ) * n - 3 ≤ f n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ ((9 / 3 : ℝ) * n - 3 ≤ f n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ ((9 / 3 : ℝ) * n - 3 ≤ f n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ ((9 / 3 : ℝ) * n - 3 ≤ f n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≥ f n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≥ f n) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≥ f n) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≥ f n) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≥ f n) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≥ f n) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≥ f n) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≥ f n) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≥ f n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≥ f n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≥ f n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≥ f n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≥ f n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≥ f n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≥ f n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((8 / 3 : ℝ) * n - 3 ≥ f n)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((8 / 3 : ℝ) * n - 3 ≥ f n)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((8 / 3 : ℝ) * n - 3 ≥ f n)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((8 / 3 : ℝ) * n - 3 ≥ f n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((8 / 3 : ℝ) * n - 3 ≥ f n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((8 / 3 : ℝ) * n - 3 ≥ f n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((8 / 3 : ℝ) * n - 3 ≥ f n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((8 / 3 : ℝ) * n - 3 ≥ f n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((8 / 3 : ℝ) * n - 3 ≥ f n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((8 / 3 : ℝ) * n - 3 ≥ f n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ ((8 / 3 : ℝ) * n - 3 ≥ f n)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ ((8 / 3 : ℝ) * n - 3 ≥ f n)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ ((8 / 3 : ℝ) * n - 3 ≥ f n)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ ((8 / 3 : ℝ) * n - 3 ≥ f n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ ((8 / 3 : ℝ) * n - 3 ≥ f n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ ((8 / 3 : ℝ) * n - 3 ≥ f n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ ((8 / 3 : ℝ) * n - 3 ≥ f n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ ((8 / 3 : ℝ) * n - 3 ≥ f n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ ((8 / 3 : ℝ) * n - 3 ≥ f n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ ((8 / 3 : ℝ) * n - 3 ≥ f n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), f n ≥ (8 / 3 : ℝ) * n - 3

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ (f n ≥ (8 / 3 : ℝ) * n - 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ (f n ≥ (8 / 3 : ℝ) * n - 3) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ (f n ≥ (8 / 3 : ℝ) * n - 3) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ (f n ≥ (8 / 3 : ℝ) * n - 3) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ (f n ≥ (8 / 3 : ℝ) * n - 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ (f n ≥ (8 / 3 : ℝ) * n - 3) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ (f n ≥ (8 / 3 : ℝ) * n - 3) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ (f n ≥ (8 / 3 : ℝ) * n - 3) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) ↔
    (∀ (n : ℕ), f n ≥ (8 / 3 : ℝ) * n - 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) ↔
    (∀ (n : ℕ), f n ≥ (8 / 3 : ℝ) * n - 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) ↔
    (∀ (n : ℕ), f n ≥ (8 / 3 : ℝ) * n - 3) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) ↔
    (∀ (n : ℕ), f n ≥ (8 / 3 : ℝ) * n - 3) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), ¬(f n < (8 / 3 : ℝ) * n - 3)

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ (¬(f n < (8 / 3 : ℝ) * n - 3)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ (¬(f n < (8 / 3 : ℝ) * n - 3)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ (¬(f n < (8 / 3 : ℝ) * n - 3)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ (¬(f n < (8 / 3 : ℝ) * n - 3)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ (¬(f n < (8 / 3 : ℝ) * n - 3)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ (¬(f n < (8 / 3 : ℝ) * n - 3)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ (¬(f n < (8 / 3 : ℝ) * n - 3)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ (¬(f n < (8 / 3 : ℝ) * n - 3)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) ↔
    (∀ (n : ℕ), ¬(f n < (8 / 3 : ℝ) * n - 3)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) ↔
    (∀ (n : ℕ), ¬(f n < (8 / 3 : ℝ) * n - 3)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) ↔
    (∀ (n : ℕ), ¬(f n < (8 / 3 : ℝ) * n - 3)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) ↔
    (∀ (n : ℕ), ¬(f n < (8 / 3 : ℝ) * n - 3)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), f n > (8 / 3 : ℝ) * n - 3

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), f n > (8 / 3 : ℝ) * n - 3) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), f n > (8 / 3 : ℝ) * n - 3) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), f n > (8 / 3 : ℝ) * n - 3) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), f n > (8 / 3 : ℝ) * n - 3) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), f n > (8 / 3 : ℝ) * n - 3) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), f n > (8 / 3 : ℝ) * n - 3) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), f n > (8 / 3 : ℝ) * n - 3) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n > (8 / 3 : ℝ) * n - 3)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n > (8 / 3 : ℝ) * n - 3)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n > (8 / 3 : ℝ) * n - 3)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n > (8 / 3 : ℝ) * n - 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n > (8 / 3 : ℝ) * n - 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n > (8 / 3 : ℝ) * n - 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n > (8 / 3 : ℝ) * n - 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n > (8 / 3 : ℝ) * n - 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n > (8 / 3 : ℝ) * n - 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n > (8 / 3 : ℝ) * n - 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ (f n > (8 / 3 : ℝ) * n - 3)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ (f n > (8 / 3 : ℝ) * n - 3)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ (f n > (8 / 3 : ℝ) * n - 3)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ (f n > (8 / 3 : ℝ) * n - 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ (f n > (8 / 3 : ℝ) * n - 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ (f n > (8 / 3 : ℝ) * n - 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ (f n > (8 / 3 : ℝ) * n - 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ (f n > (8 / 3 : ℝ) * n - 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ (f n > (8 / 3 : ℝ) * n - 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ (f n > (8 / 3 : ℝ) * n - 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), f n ≥ (9 / 3 : ℝ) * n - 3

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), f n ≥ (9 / 3 : ℝ) * n - 3) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), f n ≥ (9 / 3 : ℝ) * n - 3) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), f n ≥ (9 / 3 : ℝ) * n - 3) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), f n ≥ (9 / 3 : ℝ) * n - 3) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), f n ≥ (9 / 3 : ℝ) * n - 3) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), f n ≥ (9 / 3 : ℝ) * n - 3) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), f n ≥ (9 / 3 : ℝ) * n - 3) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) →
    (∀ (n : ℕ), f n ≥ (9 / 3 : ℝ) * n - 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) →
    (∀ (n : ℕ), f n ≥ (9 / 3 : ℝ) * n - 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) →
    (∀ (n : ℕ), f n ≥ (9 / 3 : ℝ) * n - 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) →
    (∀ (n : ℕ), f n ≥ (9 / 3 : ℝ) * n - 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) →
    (∀ (n : ℕ), f n ≥ (9 / 3 : ℝ) * n - 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) →
    (∀ (n : ℕ), f n ≥ (9 / 3 : ℝ) * n - 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) →
    (∀ (n : ℕ), f n ≥ (9 / 3 : ℝ) * n - 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n ≥ (9 / 3 : ℝ) * n - 3)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n ≥ (9 / 3 : ℝ) * n - 3)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n ≥ (9 / 3 : ℝ) * n - 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n ≥ (9 / 3 : ℝ) * n - 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n ≥ (9 / 3 : ℝ) * n - 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n ≥ (9 / 3 : ℝ) * n - 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n ≥ (9 / 3 : ℝ) * n - 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n ≥ (9 / 3 : ℝ) * n - 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n ≥ (9 / 3 : ℝ) * n - 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ (f n ≥ (9 / 3 : ℝ) * n - 3)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ (f n ≥ (9 / 3 : ℝ) * n - 3)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ (f n ≥ (9 / 3 : ℝ) * n - 3)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ (f n ≥ (9 / 3 : ℝ) * n - 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ (f n ≥ (9 / 3 : ℝ) * n - 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ (f n ≥ (9 / 3 : ℝ) * n - 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ (f n ≥ (9 / 3 : ℝ) * n - 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ (f n ≥ (9 / 3 : ℝ) * n - 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ (f n ≥ (9 / 3 : ℝ) * n - 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ (f n ≥ (9 / 3 : ℝ) * n - 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), f n ≤ (8 / 3 : ℝ) * n - 3

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), f n ≤ (8 / 3 : ℝ) * n - 3) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), f n ≤ (8 / 3 : ℝ) * n - 3) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), f n ≤ (8 / 3 : ℝ) * n - 3) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), f n ≤ (8 / 3 : ℝ) * n - 3) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), f n ≤ (8 / 3 : ℝ) * n - 3) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), f n ≤ (8 / 3 : ℝ) * n - 3) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), f n ≤ (8 / 3 : ℝ) * n - 3) →
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) →
    (∀ (n : ℕ), f n ≤ (8 / 3 : ℝ) * n - 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) →
    (∀ (n : ℕ), f n ≤ (8 / 3 : ℝ) * n - 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) →
    (∀ (n : ℕ), f n ≤ (8 / 3 : ℝ) * n - 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) →
    (∀ (n : ℕ), f n ≤ (8 / 3 : ℝ) * n - 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) →
    (∀ (n : ℕ), f n ≤ (8 / 3 : ℝ) * n - 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) →
    (∀ (n : ℕ), f n ≤ (8 / 3 : ℝ) * n - 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), (8 / 3 : ℝ) * n - 3 ≤ f n) →
    (∀ (n : ℕ), f n ≤ (8 / 3 : ℝ) * n - 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n ≤ (8 / 3 : ℝ) * n - 3)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n ≤ (8 / 3 : ℝ) * n - 3)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n ≤ (8 / 3 : ℝ) * n - 3)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n ≤ (8 / 3 : ℝ) * n - 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n ≤ (8 / 3 : ℝ) * n - 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n ≤ (8 / 3 : ℝ) * n - 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n ≤ (8 / 3 : ℝ) * n - 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n ≤ (8 / 3 : ℝ) * n - 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n ≤ (8 / 3 : ℝ) * n - 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(f n ≤ (8 / 3 : ℝ) * n - 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ (f n ≤ (8 / 3 : ℝ) * n - 3)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ (f n ≤ (8 / 3 : ℝ) * n - 3)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ (f n ≤ (8 / 3 : ℝ) * n - 3)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ (f n ≤ (8 / 3 : ℝ) * n - 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ (f n ≤ (8 / 3 : ℝ) * n - 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ (f n ≤ (8 / 3 : ℝ) * n - 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ (f n ≤ (8 / 3 : ℝ) * n - 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ (f n ≤ (8 / 3 : ℝ) * n - 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ (f n ≤ (8 / 3 : ℝ) * n - 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((8 / 3 : ℝ) * n - 3 ≤ f n) ↔ (f n ≤ (8 / 3 : ℝ) * n - 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

#eval "FIN_CERTIFICAR"
