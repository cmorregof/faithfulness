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

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k < A.card

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k < A.card) →
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k < A.card) →
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k < A.card) →
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k < A.card) →
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k < A.card) →
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k < A.card) →
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k < A.card) →
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B : Finset ℤ) (k : ℤ) (hk_pos : 0 < k), Overlap A B k ≤ A.card

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) →
    (∀ (A B : Finset ℤ) (k : ℤ) (hk_pos : 0 < k), Overlap A B k ≤ A.card) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) →
    (∀ (A B : Finset ℤ) (k : ℤ) (hk_pos : 0 < k), Overlap A B k ≤ A.card) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) →
    (∀ (A B : Finset ℤ) (k : ℤ) (hk_pos : 0 < k), Overlap A B k ≤ A.card) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) →
    (∀ (A B : Finset ℤ) (k : ℤ) (hk_pos : 0 < k), Overlap A B k ≤ A.card) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) →
    (∀ (A B : Finset ℤ) (k : ℤ) (hk_pos : 0 < k), Overlap A B k ≤ A.card) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) →
    (∀ (A B : Finset ℤ) (k : ℤ) (hk_pos : 0 < k), Overlap A B k ≤ A.card) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) →
    (∀ (A B : Finset ℤ) (k : ℤ) (hk_pos : 0 < k), Overlap A B k ≤ A.card) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (A B : Finset ℤ) (k : ℤ)  :
    (True) ↔ (0 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (A B : Finset ℤ) (k : ℤ)  :
    (True) ↔ (0 < k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (A B : Finset ℤ) (k : ℤ)  :
    (True) ↔ (0 < k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (A B : Finset ℤ) (k : ℤ)  :
    (True) ↔ (0 < k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (A B : Finset ℤ) (k : ℤ)  :
    (True) ↔ (0 < k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (A B : Finset ℤ) (k : ℤ)  :
    (True) ↔ (0 < k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (A B : Finset ℤ) (k : ℤ)  :
    (True) ↔ (0 < k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℤ), (¬((True) ↔ (0 < k))) :=
  ⟨(0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℤ), (¬((True) ↔ (0 < k))) :=
  ⟨(-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℤ), (¬((True) ↔ (0 < k))) :=
  ⟨(1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℤ), (¬((True) ↔ (0 < k))) :=
  ⟨(2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℤ), (¬((True) ↔ (0 < k))) :=
  ⟨(-2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℤ), (¬((True) ↔ (0 < k))) :=
  ⟨(3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℤ), ¬((True) ↔ (0 < k)) :=
  ⟨(0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℤ), ¬((True) ↔ (0 < k)) :=
  ⟨(-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℤ), ¬((True) ↔ (0 < k)) :=
  ⟨(1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℤ), ¬((True) ↔ (0 < k)) :=
  ⟨(2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℤ), ¬((True) ↔ (0 < k)) :=
  ⟨(-2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℤ), ¬((True) ↔ (0 < k)) :=
  ⟨(3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≥ A.card

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≥ A.card) →
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≥ A.card) →
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≥ A.card) →
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≥ A.card) →
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≥ A.card) →
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≥ A.card) →
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≥ A.card) →
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) →
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≥ A.card) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) →
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≥ A.card) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) →
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≥ A.card) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) →
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≥ A.card) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) →
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≥ A.card) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) →
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≥ A.card) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) →
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≥ A.card) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B : Finset ℤ) (k : ℤ), A.card ≥ Overlap A B k

set_option maxHeartbeats 200000 in
example (A B : Finset ℤ) (k : ℤ) :
    (Overlap A B k ≤ A.card) ↔ (A.card ≥ Overlap A B k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (A B : Finset ℤ) (k : ℤ) :
    (Overlap A B k ≤ A.card) ↔ (A.card ≥ Overlap A B k) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (A B : Finset ℤ) (k : ℤ) :
    (Overlap A B k ≤ A.card) ↔ (A.card ≥ Overlap A B k) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (A B : Finset ℤ) (k : ℤ) :
    (Overlap A B k ≤ A.card) ↔ (A.card ≥ Overlap A B k) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (A B : Finset ℤ) (k : ℤ) :
    (Overlap A B k ≤ A.card) ↔ (A.card ≥ Overlap A B k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (A B : Finset ℤ) (k : ℤ) :
    (Overlap A B k ≤ A.card) ↔ (A.card ≥ Overlap A B k) := by
  omega

set_option maxHeartbeats 200000 in
example (A B : Finset ℤ) (k : ℤ) :
    (Overlap A B k ≤ A.card) ↔ (A.card ≥ Overlap A B k) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (A B : Finset ℤ) (k : ℤ) :
    (Overlap A B k ≤ A.card) ↔ (A.card ≥ Overlap A B k) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) ↔
    (∀ (A B : Finset ℤ) (k : ℤ), A.card ≥ Overlap A B k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) ↔
    (∀ (A B : Finset ℤ) (k : ℤ), A.card ≥ Overlap A B k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) ↔
    (∀ (A B : Finset ℤ) (k : ℤ), A.card ≥ Overlap A B k) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) ↔
    (∀ (A B : Finset ℤ) (k : ℤ), A.card ≥ Overlap A B k) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B : Finset ℤ) (k : ℤ), A.card > Overlap A B k

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), A.card > Overlap A B k) →
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), A.card > Overlap A B k) →
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), A.card > Overlap A B k) →
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), A.card > Overlap A B k) →
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), A.card > Overlap A B k) →
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), A.card > Overlap A B k) →
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), A.card > Overlap A B k) →
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B : Finset ℤ) (k : ℤ), A.card ≤ Overlap A B k

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), A.card ≤ Overlap A B k) →
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), A.card ≤ Overlap A B k) →
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), A.card ≤ Overlap A B k) →
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), A.card ≤ Overlap A B k) →
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), A.card ≤ Overlap A B k) →
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), A.card ≤ Overlap A B k) →
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), A.card ≤ Overlap A B k) →
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) →
    (∀ (A B : Finset ℤ) (k : ℤ), A.card ≤ Overlap A B k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) →
    (∀ (A B : Finset ℤ) (k : ℤ), A.card ≤ Overlap A B k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) →
    (∀ (A B : Finset ℤ) (k : ℤ), A.card ≤ Overlap A B k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) →
    (∀ (A B : Finset ℤ) (k : ℤ), A.card ≤ Overlap A B k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) →
    (∀ (A B : Finset ℤ) (k : ℤ), A.card ≤ Overlap A B k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) →
    (∀ (A B : Finset ℤ) (k : ℤ), A.card ≤ Overlap A B k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset ℤ) (k : ℤ), Overlap A B k ≤ A.card) →
    (∀ (A B : Finset ℤ) (k : ℤ), A.card ≤ Overlap A B k) := by
  intro h; intros; aesop

#eval "FIN_CERTIFICAR"
