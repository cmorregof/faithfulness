import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 36

*References:*
 - [erdosproblems.com/36](https://www.erdosproblems.com/36)
 - [Wikipedial: Minimum overlap problem](https://en.wikipedia.org/wiki/Minimum_overlap_problem)
-/

section

open scoped Topology
open Filter
namespace Erdos36

/--
The number of solutions to the equation $a - b = k$, for $a \in A$ and $b \in B$.
This represents the "overlap" between sets $A$ and $B$ for a given difference $k$.
-/
def Overlap (A B : Finset ℤ) (k : ℤ) : ℕ := ((A.product B).filter <| fun (a, b) => a - b = k).card

/--
The maximum overlap for a given pair of sets $A$ and $B$,
taken over all possible integer differences $k$.
-/
noncomputable def MaxOverlap (A B : Finset ℤ) : ℕ := iSup <| Overlap A B

/--
Let $A$ and $B$ be two complementary subsets, a splitting of the numbers $\{1, 2, \dots, 2n\}$,
such that both have the same cardinality $n$.
Define $M(n)$ to be the minimum `MaxOverlap` that can be achieved,
ranging over all such partitions $(A, B)$.
-/
noncomputable def M (n : ℕ) : ℕ :=
  sInf {MaxOverlap A B | (A : Finset ℤ) (B : Finset ℤ)
    (_disjoint : Disjoint A B)
    (_union : A ∪ B = Finset.Icc (1 : ℤ) (2 * n))
    (_same_card : A.card = B.card)}

/-- A computable stand-in for `MaxOverlap`. `Overlap` is already computable; the only obstacle
is the `iSup`, and `maxOverlap_eq_sup` says it agrees with this `Finset.sup`. -/
private def maxOverlapC (A B : Finset ℤ) : ℕ :=
  ((A ×ˢ B).image fun p => p.1 - p.2).sup (Overlap A B)

/-- The `n`-element subsets of `{1, …, 2n}`. -/
private def parts (n : ℕ) : Finset (Finset ℤ) :=
  letI : Preorder ℤ := Int.instLinearOrder.toPreorder
  (Finset.Icc (1 : ℤ) (2 * n)).powerset.filter fun A => A.card = n

/--
The quotient of the minimum maximum overlap $M(N)$ by $N$. The central question of the
minimum overlap problem is to determine the asymptotic behavior of this quotient as $N \to \infty$.
-/
noncomputable def MinOverlapQuotient (N : ℕ) := (M N : ℝ) / N

set_option maxHeartbeats 200000 in
example : Prop :=
  0.379005 ≤ atTop.liminf MinOverlapQuotient

set_option maxHeartbeats 200000 in
example : Prop :=
  0.379005 < atTop.liminf MinOverlapQuotient

set_option maxHeartbeats 200000 in
example :
    (0.379005 < atTop.liminf MinOverlapQuotient) →
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (0.379005 < atTop.liminf MinOverlapQuotient) →
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (0.379005 < atTop.liminf MinOverlapQuotient) →
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (0.379005 < atTop.liminf MinOverlapQuotient) →
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (0.379005 < atTop.liminf MinOverlapQuotient) →
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (0.379005 < atTop.liminf MinOverlapQuotient) →
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (0.379005 < atTop.liminf MinOverlapQuotient) →
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (¬(0.379005 < atTop.liminf MinOverlapQuotient)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (¬(0.379005 < atTop.liminf MinOverlapQuotient)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((0.379005 ≤ atTop.liminf MinOverlapQuotient) ↔ (0.379005 < atTop.liminf MinOverlapQuotient)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((0.379005 ≤ atTop.liminf MinOverlapQuotient) ↔ (0.379005 < atTop.liminf MinOverlapQuotient)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  0.379005 ≤ atTop.liminf MinOverlapQuotient

set_option maxHeartbeats 200000 in
example : Prop :=
  0.379005 ≥ atTop.liminf MinOverlapQuotient

set_option maxHeartbeats 200000 in
example :
    (0.379005 ≥ atTop.liminf MinOverlapQuotient) →
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (0.379005 ≥ atTop.liminf MinOverlapQuotient) →
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (0.379005 ≥ atTop.liminf MinOverlapQuotient) →
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (0.379005 ≥ atTop.liminf MinOverlapQuotient) →
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (0.379005 ≥ atTop.liminf MinOverlapQuotient) →
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (0.379005 ≥ atTop.liminf MinOverlapQuotient) →
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (0.379005 ≥ atTop.liminf MinOverlapQuotient) →
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) →
    (0.379005 ≥ atTop.liminf MinOverlapQuotient) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) →
    (0.379005 ≥ atTop.liminf MinOverlapQuotient) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) →
    (0.379005 ≥ atTop.liminf MinOverlapQuotient) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) →
    (0.379005 ≥ atTop.liminf MinOverlapQuotient) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) →
    (0.379005 ≥ atTop.liminf MinOverlapQuotient) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) →
    (0.379005 ≥ atTop.liminf MinOverlapQuotient) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) →
    (0.379005 ≥ atTop.liminf MinOverlapQuotient) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (¬(0.379005 ≥ atTop.liminf MinOverlapQuotient)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (¬(0.379005 ≥ atTop.liminf MinOverlapQuotient)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((0.379005 ≤ atTop.liminf MinOverlapQuotient) ↔ (0.379005 ≥ atTop.liminf MinOverlapQuotient)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((0.379005 ≤ atTop.liminf MinOverlapQuotient) ↔ (0.379005 ≥ atTop.liminf MinOverlapQuotient)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  0.379005 ≤ atTop.liminf MinOverlapQuotient

set_option maxHeartbeats 200000 in
example : Prop :=
  atTop.liminf MinOverlapQuotient ≥ 0.379005

set_option maxHeartbeats 200000 in
example  :
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) ↔ (atTop.liminf MinOverlapQuotient ≥ 0.379005) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example  :
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) ↔ (atTop.liminf MinOverlapQuotient ≥ 0.379005) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example  :
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) ↔ (atTop.liminf MinOverlapQuotient ≥ 0.379005) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example  :
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) ↔ (atTop.liminf MinOverlapQuotient ≥ 0.379005) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example  :
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) ↔ (atTop.liminf MinOverlapQuotient ≥ 0.379005) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example  :
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) ↔ (atTop.liminf MinOverlapQuotient ≥ 0.379005) := by
  omega

set_option maxHeartbeats 200000 in
example  :
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) ↔ (atTop.liminf MinOverlapQuotient ≥ 0.379005) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example  :
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) ↔ (atTop.liminf MinOverlapQuotient ≥ 0.379005) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) ↔
    (atTop.liminf MinOverlapQuotient ≥ 0.379005) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) ↔
    (atTop.liminf MinOverlapQuotient ≥ 0.379005) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) ↔
    (atTop.liminf MinOverlapQuotient ≥ 0.379005) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) ↔
    (atTop.liminf MinOverlapQuotient ≥ 0.379005) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  0.379005 ≤ atTop.liminf MinOverlapQuotient

set_option maxHeartbeats 200000 in
example : Prop :=
  ¬(atTop.liminf MinOverlapQuotient < 0.379005)

set_option maxHeartbeats 200000 in
example  :
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) ↔ (¬(atTop.liminf MinOverlapQuotient < 0.379005)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example  :
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) ↔ (¬(atTop.liminf MinOverlapQuotient < 0.379005)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example  :
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) ↔ (¬(atTop.liminf MinOverlapQuotient < 0.379005)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example  :
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) ↔ (¬(atTop.liminf MinOverlapQuotient < 0.379005)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example  :
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) ↔ (¬(atTop.liminf MinOverlapQuotient < 0.379005)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example  :
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) ↔ (¬(atTop.liminf MinOverlapQuotient < 0.379005)) := by
  omega

set_option maxHeartbeats 200000 in
example  :
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) ↔ (¬(atTop.liminf MinOverlapQuotient < 0.379005)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example  :
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) ↔ (¬(atTop.liminf MinOverlapQuotient < 0.379005)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) ↔
    (¬(atTop.liminf MinOverlapQuotient < 0.379005)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) ↔
    (¬(atTop.liminf MinOverlapQuotient < 0.379005)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) ↔
    (¬(atTop.liminf MinOverlapQuotient < 0.379005)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) ↔
    (¬(atTop.liminf MinOverlapQuotient < 0.379005)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  0.379005 ≤ atTop.liminf MinOverlapQuotient

set_option maxHeartbeats 200000 in
example : Prop :=
  atTop.liminf MinOverlapQuotient > 0.379005

set_option maxHeartbeats 200000 in
example :
    (atTop.liminf MinOverlapQuotient > 0.379005) →
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (atTop.liminf MinOverlapQuotient > 0.379005) →
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (atTop.liminf MinOverlapQuotient > 0.379005) →
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (atTop.liminf MinOverlapQuotient > 0.379005) →
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (atTop.liminf MinOverlapQuotient > 0.379005) →
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (atTop.liminf MinOverlapQuotient > 0.379005) →
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (atTop.liminf MinOverlapQuotient > 0.379005) →
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (¬(atTop.liminf MinOverlapQuotient > 0.379005)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (¬(atTop.liminf MinOverlapQuotient > 0.379005)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((0.379005 ≤ atTop.liminf MinOverlapQuotient) ↔ (atTop.liminf MinOverlapQuotient > 0.379005)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((0.379005 ≤ atTop.liminf MinOverlapQuotient) ↔ (atTop.liminf MinOverlapQuotient > 0.379005)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  0.379005 ≤ atTop.liminf MinOverlapQuotient

set_option maxHeartbeats 200000 in
example : Prop :=
  atTop.liminf MinOverlapQuotient ≤ 0.379005

set_option maxHeartbeats 200000 in
example :
    (atTop.liminf MinOverlapQuotient ≤ 0.379005) →
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (atTop.liminf MinOverlapQuotient ≤ 0.379005) →
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (atTop.liminf MinOverlapQuotient ≤ 0.379005) →
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (atTop.liminf MinOverlapQuotient ≤ 0.379005) →
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (atTop.liminf MinOverlapQuotient ≤ 0.379005) →
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (atTop.liminf MinOverlapQuotient ≤ 0.379005) →
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (atTop.liminf MinOverlapQuotient ≤ 0.379005) →
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) →
    (atTop.liminf MinOverlapQuotient ≤ 0.379005) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) →
    (atTop.liminf MinOverlapQuotient ≤ 0.379005) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) →
    (atTop.liminf MinOverlapQuotient ≤ 0.379005) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) →
    (atTop.liminf MinOverlapQuotient ≤ 0.379005) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) →
    (atTop.liminf MinOverlapQuotient ≤ 0.379005) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) →
    (atTop.liminf MinOverlapQuotient ≤ 0.379005) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (0.379005 ≤ atTop.liminf MinOverlapQuotient) →
    (atTop.liminf MinOverlapQuotient ≤ 0.379005) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (¬(atTop.liminf MinOverlapQuotient ≤ 0.379005)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (¬(atTop.liminf MinOverlapQuotient ≤ 0.379005)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((0.379005 ≤ atTop.liminf MinOverlapQuotient) ↔ (atTop.liminf MinOverlapQuotient ≤ 0.379005)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((0.379005 ≤ atTop.liminf MinOverlapQuotient) ↔ (atTop.liminf MinOverlapQuotient ≤ 0.379005)) :=
  by decide

#eval "FIN_CERTIFICAR"
