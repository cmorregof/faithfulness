import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 819

*References:*
- [erdosproblems.com/819](https://www.erdosproblems.com/819)
- [Er91] Erdős, P., *Problems and results in combinatorial analysis and combinatorial number
  theory*. Graph theory, combinatorics, and applications, Vol. 1 (Kalamazoo, MI, 1988) (1991),
  397-406.
- [ErFr91] Erdős, P. and Freud, R., *On sums of a Sidon-sequence*. J. Number Theory 38 (1991),
  196-205.
-/

section

open Filter Asymptotics
open scoped Finset Pointwise

namespace Erdos819

/-- $f(N)$ is the maximum of $\lvert (A + A) \cap [1, N] \rvert$ over all
$A \subseteq \{1, \ldots, N\}$ with $\lvert A \rvert = \lfloor N^{1/2} \rfloor$, where
$\lfloor N^{1/2} \rfloor$ is `Nat.sqrt N`. Such sets exist for every $N$, since
$\lfloor N^{1/2} \rfloor \leq N$, so the maximum is over a nonempty family. -/
def f (N : ℕ) : ℕ :=
  (Finset.powersetCard (Nat.sqrt N) (Finset.Icc 1 N)).sup
    fun A ↦ #((A + A) ∩ Finset.Icc 1 N)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ), #(A + A) < (#A + 1).choose 2

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) < (#A + 1).choose 2) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) < (#A + 1).choose 2) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) < (#A + 1).choose 2) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) < (#A + 1).choose 2) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) < (#A + 1).choose 2) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) < (#A + 1).choose 2) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) < (#A + 1).choose 2) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 3

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 3) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 3) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 3) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 3) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 3) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 3) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 3) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ), #(A + A) ≥ (#A + 1).choose 2

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) ≥ (#A + 1).choose 2) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) ≥ (#A + 1).choose 2) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) ≥ (#A + 1).choose 2) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) ≥ (#A + 1).choose 2) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) ≥ (#A + 1).choose 2) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) ≥ (#A + 1).choose 2) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) ≥ (#A + 1).choose 2) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) →
    (∀ (A : Finset ℕ), #(A + A) ≥ (#A + 1).choose 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) →
    (∀ (A : Finset ℕ), #(A + A) ≥ (#A + 1).choose 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) →
    (∀ (A : Finset ℕ), #(A + A) ≥ (#A + 1).choose 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) →
    (∀ (A : Finset ℕ), #(A + A) ≥ (#A + 1).choose 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) →
    (∀ (A : Finset ℕ), #(A + A) ≥ (#A + 1).choose 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) →
    (∀ (A : Finset ℕ), #(A + A) ≥ (#A + 1).choose 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) →
    (∀ (A : Finset ℕ), #(A + A) ≥ (#A + 1).choose 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ), (#A + 1).choose 2 ≥ #(A + A)

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) :
    (#(A + A) ≤ (#A + 1).choose 2) ↔ ((#A + 1).choose 2 ≥ #(A + A)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) :
    (#(A + A) ≤ (#A + 1).choose 2) ↔ ((#A + 1).choose 2 ≥ #(A + A)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) :
    (#(A + A) ≤ (#A + 1).choose 2) ↔ ((#A + 1).choose 2 ≥ #(A + A)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) :
    (#(A + A) ≤ (#A + 1).choose 2) ↔ ((#A + 1).choose 2 ≥ #(A + A)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) :
    (#(A + A) ≤ (#A + 1).choose 2) ↔ ((#A + 1).choose 2 ≥ #(A + A)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) :
    (#(A + A) ≤ (#A + 1).choose 2) ↔ ((#A + 1).choose 2 ≥ #(A + A)) := by
  omega

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) :
    (#(A + A) ≤ (#A + 1).choose 2) ↔ ((#A + 1).choose 2 ≥ #(A + A)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) :
    (#(A + A) ≤ (#A + 1).choose 2) ↔ ((#A + 1).choose 2 ≥ #(A + A)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) ↔
    (∀ (A : Finset ℕ), (#A + 1).choose 2 ≥ #(A + A)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) ↔
    (∀ (A : Finset ℕ), (#A + 1).choose 2 ≥ #(A + A)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) ↔
    (∀ (A : Finset ℕ), (#A + 1).choose 2 ≥ #(A + A)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) ↔
    (∀ (A : Finset ℕ), (#A + 1).choose 2 ≥ #(A + A)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ), (#A + 1).choose 2 > #(A + A)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), (#A + 1).choose 2 > #(A + A)) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), (#A + 1).choose 2 > #(A + A)) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), (#A + 1).choose 2 > #(A + A)) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), (#A + 1).choose 2 > #(A + A)) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), (#A + 1).choose 2 > #(A + A)) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), (#A + 1).choose 2 > #(A + A)) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), (#A + 1).choose 2 > #(A + A)) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ), (#A + 1).choose 3 ≥ #(A + A)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), (#A + 1).choose 3 ≥ #(A + A)) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), (#A + 1).choose 3 ≥ #(A + A)) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), (#A + 1).choose 3 ≥ #(A + A)) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), (#A + 1).choose 3 ≥ #(A + A)) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), (#A + 1).choose 3 ≥ #(A + A)) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), (#A + 1).choose 3 ≥ #(A + A)) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), (#A + 1).choose 3 ≥ #(A + A)) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) →
    (∀ (A : Finset ℕ), (#A + 1).choose 3 ≥ #(A + A)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) →
    (∀ (A : Finset ℕ), (#A + 1).choose 3 ≥ #(A + A)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) →
    (∀ (A : Finset ℕ), (#A + 1).choose 3 ≥ #(A + A)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) →
    (∀ (A : Finset ℕ), (#A + 1).choose 3 ≥ #(A + A)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) →
    (∀ (A : Finset ℕ), (#A + 1).choose 3 ≥ #(A + A)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) →
    (∀ (A : Finset ℕ), (#A + 1).choose 3 ≥ #(A + A)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) →
    (∀ (A : Finset ℕ), (#A + 1).choose 3 ≥ #(A + A)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ), (#A + 1).choose 2 ≤ #(A + A)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), (#A + 1).choose 2 ≤ #(A + A)) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), (#A + 1).choose 2 ≤ #(A + A)) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), (#A + 1).choose 2 ≤ #(A + A)) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), (#A + 1).choose 2 ≤ #(A + A)) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), (#A + 1).choose 2 ≤ #(A + A)) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), (#A + 1).choose 2 ≤ #(A + A)) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), (#A + 1).choose 2 ≤ #(A + A)) →
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) →
    (∀ (A : Finset ℕ), (#A + 1).choose 2 ≤ #(A + A)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) →
    (∀ (A : Finset ℕ), (#A + 1).choose 2 ≤ #(A + A)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) →
    (∀ (A : Finset ℕ), (#A + 1).choose 2 ≤ #(A + A)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) →
    (∀ (A : Finset ℕ), (#A + 1).choose 2 ≤ #(A + A)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) →
    (∀ (A : Finset ℕ), (#A + 1).choose 2 ≤ #(A + A)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) →
    (∀ (A : Finset ℕ), (#A + 1).choose 2 ≤ #(A + A)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ), #(A + A) ≤ (#A + 1).choose 2) →
    (∀ (A : Finset ℕ), (#A + 1).choose 2 ≤ #(A + A)) := by
  intro h; intros; aesop

#eval "FIN_CERTIFICAR"
