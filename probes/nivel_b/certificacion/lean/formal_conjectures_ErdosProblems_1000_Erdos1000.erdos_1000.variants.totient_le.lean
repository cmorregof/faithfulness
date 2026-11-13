import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 1000

*References:*
- [erdosproblems.com/1000](https://www.erdosproblems.com/1000)
- [Ca50b] Cassels, J. W. S., *Some metrical theorems in Diophantine approximation. I*. Proc.
  Cambridge Philos. Soc. (1950), 209-218.
- [Er64b] Erdős, P., *Problems and results on diophantine approximations*. Compositio Math. (1964),
  52-65.
- [Ha] Haight, J. A., *Metric Diophantine approximation and related topics*. PhD thesis.
-/

section

open Filter Topology

namespace Erdos1000

/--
Given an infinite sequence of positive integers $A = \{n_1 < n_2 < \cdots\}$, `phiSeq n k` is
$\phi_A(k)$: the number of $1\leq m\leq n_k$ such that $\frac{m}{n_k}$ cannot be written as
$\frac{b}{n_j}$ for any integer $b$ and any $1\leq j<k$; equivalently,
$$
\frac{n_k}{(m,n_k)}\nmid n_j
$$
for all $1\leq j<k$.
-/
def phiSeq (n : ℕ → ℕ) (k : ℕ) : ℕ :=
  ((Finset.Icc 1 (n k)).filter fun m => ∀ j < k, ¬ (n k / Nat.gcd m (n k)) ∣ n j).card

/--
The average $\frac{1}{N}\sum_{k\leq N}\frac{\phi_A(k)}{n_k}$.
-/
noncomputable def phiAvg (n : ℕ → ℕ) (N : ℕ) : ℝ :=
  (∑ k ∈ Finset.range N, (phiSeq n k : ℝ) / (n k : ℝ)) / (N : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ → ℕ) (hn : StrictMono n) (k : ℕ), (n k).totient ≤ phiSeq n k

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (k : ℕ), (n k).totient ≤ phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (k : ℕ), (n k).totient ≤ phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (k : ℕ), (n k).totient ≤ phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (k : ℕ), (n k).totient ≤ phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (k : ℕ), (n k).totient ≤ phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (k : ℕ), (n k).totient ≤ phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (k : ℕ), (n k).totient ≤ phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ → ℕ) (k : ℕ) (hn : StrictMono n) :
    (0 < n 0) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ → ℕ) (k : ℕ) (hn : StrictMono n) :
    (0 < n 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ → ℕ) (k : ℕ) (hn : StrictMono n) :
    (0 < n 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ → ℕ) (k : ℕ) (hn : StrictMono n) :
    (0 < n 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ → ℕ) (k : ℕ) (hn : StrictMono n) :
    (0 < n 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ → ℕ) (k : ℕ) (hn : StrictMono n) :
    (0 < n 0) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ → ℕ) (k : ℕ) (hn : StrictMono n) :
    (0 < n 0) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient < phiSeq n k

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient < phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient < phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient < phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient < phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient < phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient < phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient < phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≥ phiSeq n k

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≥ phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≥ phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≥ phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≥ phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≥ phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≥ phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≥ phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≥ phiSeq n k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≥ phiSeq n k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≥ phiSeq n k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≥ phiSeq n k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≥ phiSeq n k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≥ phiSeq n k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≥ phiSeq n k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : n 0 > 0) (k : ℕ), (n k).totient ≤ phiSeq n k

set_option maxHeartbeats 200000 in
example (n : ℕ → ℕ) (k : ℕ) :
    (0 < n 0) ↔ (n 0 > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ → ℕ) (k : ℕ) :
    (0 < n 0) ↔ (n 0 > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ → ℕ) (k : ℕ) :
    (0 < n 0) ↔ (n 0 > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ → ℕ) (k : ℕ) :
    (0 < n 0) ↔ (n 0 > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ → ℕ) (k : ℕ) :
    (0 < n 0) ↔ (n 0 > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ → ℕ) (k : ℕ) :
    (0 < n 0) ↔ (n 0 > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ → ℕ) (k : ℕ) :
    (0 < n 0) ↔ (n 0 > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ → ℕ) (k : ℕ) :
    (0 < n 0) ↔ (n 0 > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) ↔
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : n 0 > 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) ↔
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : n 0 > 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) ↔
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : n 0 > 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) ↔
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : n 0 > 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), phiSeq n k ≥ (n k).totient

set_option maxHeartbeats 200000 in
example (n : ℕ → ℕ) (k : ℕ) :
    ((n k).totient ≤ phiSeq n k) ↔ (phiSeq n k ≥ (n k).totient) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ → ℕ) (k : ℕ) :
    ((n k).totient ≤ phiSeq n k) ↔ (phiSeq n k ≥ (n k).totient) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ → ℕ) (k : ℕ) :
    ((n k).totient ≤ phiSeq n k) ↔ (phiSeq n k ≥ (n k).totient) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ → ℕ) (k : ℕ) :
    ((n k).totient ≤ phiSeq n k) ↔ (phiSeq n k ≥ (n k).totient) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ → ℕ) (k : ℕ) :
    ((n k).totient ≤ phiSeq n k) ↔ (phiSeq n k ≥ (n k).totient) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ → ℕ) (k : ℕ) :
    ((n k).totient ≤ phiSeq n k) ↔ (phiSeq n k ≥ (n k).totient) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ → ℕ) (k : ℕ) :
    ((n k).totient ≤ phiSeq n k) ↔ (phiSeq n k ≥ (n k).totient) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ → ℕ) (k : ℕ) :
    ((n k).totient ≤ phiSeq n k) ↔ (phiSeq n k ≥ (n k).totient) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) ↔
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), phiSeq n k ≥ (n k).totient) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) ↔
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), phiSeq n k ≥ (n k).totient) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) ↔
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), phiSeq n k ≥ (n k).totient) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) ↔
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), phiSeq n k ≥ (n k).totient) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ → ℕ) (hn0 : 0 < n 0) (hn : StrictMono n) (k : ℕ), (n k).totient ≤ phiSeq n k

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) ↔
    (∀ (n : ℕ → ℕ) (hn0 : 0 < n 0) (hn : StrictMono n) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) ↔
    (∀ (n : ℕ → ℕ) (hn0 : 0 < n 0) (hn : StrictMono n) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) ↔
    (∀ (n : ℕ → ℕ) (hn0 : 0 < n 0) (hn : StrictMono n) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) ↔
    (∀ (n : ℕ → ℕ) (hn0 : 0 < n 0) (hn : StrictMono n) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ → ℕ) (hn₀ : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) ↔
    (∀ (n : ℕ → ℕ) (hn₀ : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) ↔
    (∀ (n : ℕ → ℕ) (hn₀ : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) ↔
    (∀ (n : ℕ → ℕ) (hn₀ : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) ↔
    (∀ (n : ℕ → ℕ) (hn₀ : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : n 0 > 0) (k : ℕ), (n k).totient < phiSeq n k

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : n 0 > 0) (k : ℕ), (n k).totient < phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : n 0 > 0) (k : ℕ), (n k).totient < phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : n 0 > 0) (k : ℕ), (n k).totient < phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : n 0 > 0) (k : ℕ), (n k).totient < phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : n 0 > 0) (k : ℕ), (n k).totient < phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : n 0 > 0) (k : ℕ), (n k).totient < phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : n 0 > 0) (k : ℕ), (n k).totient < phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : n 0 > 0) (k : ℕ), (n k).totient ≥ phiSeq n k

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : n 0 > 0) (k : ℕ), (n k).totient ≥ phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : n 0 > 0) (k : ℕ), (n k).totient ≥ phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : n 0 > 0) (k : ℕ), (n k).totient ≥ phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : n 0 > 0) (k : ℕ), (n k).totient ≥ phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : n 0 > 0) (k : ℕ), (n k).totient ≥ phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : n 0 > 0) (k : ℕ), (n k).totient ≥ phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : n 0 > 0) (k : ℕ), (n k).totient ≥ phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : n 0 > 0) (k : ℕ), (n k).totient ≥ phiSeq n k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : n 0 > 0) (k : ℕ), (n k).totient ≥ phiSeq n k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : n 0 > 0) (k : ℕ), (n k).totient ≥ phiSeq n k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : n 0 > 0) (k : ℕ), (n k).totient ≥ phiSeq n k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : n 0 > 0) (k : ℕ), (n k).totient ≥ phiSeq n k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : n 0 > 0) (k : ℕ), (n k).totient ≥ phiSeq n k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : n 0 > 0) (k : ℕ), (n k).totient ≥ phiSeq n k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), phiSeq n k > (n k).totient

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), phiSeq n k > (n k).totient) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), phiSeq n k > (n k).totient) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), phiSeq n k > (n k).totient) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), phiSeq n k > (n k).totient) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), phiSeq n k > (n k).totient) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), phiSeq n k > (n k).totient) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), phiSeq n k > (n k).totient) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), phiSeq n k ≤ (n k).totient

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), phiSeq n k ≤ (n k).totient) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), phiSeq n k ≤ (n k).totient) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), phiSeq n k ≤ (n k).totient) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), phiSeq n k ≤ (n k).totient) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), phiSeq n k ≤ (n k).totient) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), phiSeq n k ≤ (n k).totient) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), phiSeq n k ≤ (n k).totient) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), phiSeq n k ≤ (n k).totient) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), phiSeq n k ≤ (n k).totient) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), phiSeq n k ≤ (n k).totient) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), phiSeq n k ≤ (n k).totient) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), phiSeq n k ≤ (n k).totient) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), phiSeq n k ≤ (n k).totient) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), (n k).totient ≤ phiSeq n k) →
    (∀ (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) (k : ℕ), phiSeq n k ≤ (n k).totient) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ → ℕ) (k : ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ → ℕ) (k : ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ → ℕ) (k : ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ → ℕ) (k : ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ → ℕ) (k : ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
