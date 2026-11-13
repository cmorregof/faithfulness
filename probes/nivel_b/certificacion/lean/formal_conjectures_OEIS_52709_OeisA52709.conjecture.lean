import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Expansion of g.f. $(1-\sqrt{1-4x-4x^2})/(2(1+x))$

The $n$-th term $a(n)$ is given by
$$a(n) = \sum_{k=0}^{n-1} \frac{1}{k+1} \binom{2k}{k} \binom{k}{n-1-k}$$

*References:*
- [A052709](https://oeis.org/A052709)-/

section

namespace OeisA52709

/-- $a(n) = \sum_{k=0}^{n-1} \frac{1}{k+1} \binom{2k}{k} \binom{k}{n-1-k}$. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, ((Nat.choose (2 * k) k) / (k + 1)) * (Nat.choose k (n - 1 - k))

/-- A list of natural numbers is composed of positive integers. -/
def isPositiveList (l : List ℕ) : Prop :=
  ∀ x ∈ l, 0 < x

/-- A list covers an initial interval of positive integers if the set of
    its elements is $\{1, 2, \dots, \max(l)\}$. -/
def coversInitialInterval (l : List ℕ) : Prop :=
  isPositiveList l ∧
  let s := l.toFinset
  match s.max with
  | some max_s => ∀ m : ℕ, 0 < m → (m ∈ s ↔ m ≤ max_s)
  | none => l.isEmpty

/-- A list has a non-decreasing subsequence of length 3 (the pattern $x \le y \le z$). -/
def hasNondecreasingPattern3 (l : List ℕ) : Prop :=
  ∃ (i j k : Fin l.length),
    i < j ∧ j < k ∧ l.get i ≤ l.get j ∧ l.get j ≤ l.get k

/-- A list avoids the pattern $x \le y \le z$ if it does not have a non-decreasing
subsequence of length 3. -/
def avoidsPatternXYZ (l : List ℕ) : Prop :=
  ¬ hasNondecreasingPattern3 l

/-- The set of sequences of length $n-1$ satisfying the conditions of the conjecture. -/
def sequencesCountedByA052709 (n : ℕ) : Set (List ℕ) :=
  { l : List ℕ | l.length = n - 1 ∧ coversInitialInterval l ∧ avoidsPatternXYZ l }

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) →
    (∀ (n : ℕ) (hn : 0 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) →
    (∀ (n : ℕ) (hn : 0 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) →
    (∀ (n : ℕ) (hn : 0 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) →
    (∀ (n : ℕ) (hn : 0 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) →
    (∀ (n : ℕ) (hn : 0 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) →
    (∀ (n : ℕ) (hn : 0 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) →
    (∀ (n : ℕ) (hn : 0 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) [Fintype (sequencesCountedByA052709 n)]  :
    (0 < n) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) [Fintype (sequencesCountedByA052709 n)]  :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) [Fintype (sequencesCountedByA052709 n)]  :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) [Fintype (sequencesCountedByA052709 n)]  :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) [Fintype (sequencesCountedByA052709 n)]  :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) [Fintype (sequencesCountedByA052709 n)]  :
    (0 < n) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) [Fintype (sequencesCountedByA052709 n)]  :
    (0 < n) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((0 < n) ↔ (True))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((0 < n) ↔ (True))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((0 < n) ↔ (True))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((0 < n) ↔ (True))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 0) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)

set_option maxHeartbeats 200000 in
example (n : ℕ) [Fintype (sequencesCountedByA052709 n)] :
    (0 < n) ↔ (n > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) [Fintype (sequencesCountedByA052709 n)] :
    (0 < n) ↔ (n > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) [Fintype (sequencesCountedByA052709 n)] :
    (0 < n) ↔ (n > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) [Fintype (sequencesCountedByA052709 n)] :
    (0 < n) ↔ (n > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) [Fintype (sequencesCountedByA052709 n)] :
    (0 < n) ↔ (n > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) [Fintype (sequencesCountedByA052709 n)] :
    (0 < n) ↔ (n > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) [Fintype (sequencesCountedByA052709 n)] :
    (0 < n) ↔ (n > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) [Fintype (sequencesCountedByA052709 n)] :
    (0 < n) ↔ (n > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) ↔
    (∀ (n : ℕ) (hn : n > 0) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) ↔
    (∀ (n : ℕ) (hn : n > 0) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) ↔
    (∀ (n : ℕ) (hn : n > 0) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) ↔
    (∀ (n : ℕ) (hn : n > 0) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn₀ : 0 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) ↔
    (∀ (n : ℕ) (hn₀ : 0 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) ↔
    (∀ (n : ℕ) (hn₀ : 0 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) ↔
    (∀ (n : ℕ) (hn₀ : 0 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) ↔
    (∀ (n : ℕ) (hn₀ : 0 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : ¬(n ≤ 0)) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)

set_option maxHeartbeats 200000 in
example (n : ℕ) [Fintype (sequencesCountedByA052709 n)] :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) [Fintype (sequencesCountedByA052709 n)] :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) [Fintype (sequencesCountedByA052709 n)] :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) [Fintype (sequencesCountedByA052709 n)] :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) [Fintype (sequencesCountedByA052709 n)] :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) [Fintype (sequencesCountedByA052709 n)] :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) [Fintype (sequencesCountedByA052709 n)] :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) [Fintype (sequencesCountedByA052709 n)] :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 0)) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 0)) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 0)) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 0)) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)

set_option maxHeartbeats 200000 in
example (n : ℕ) [Fintype (sequencesCountedByA052709 n)] :
    (0 < n) ↔ (1 ≤ n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) [Fintype (sequencesCountedByA052709 n)] :
    (0 < n) ↔ (1 ≤ n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) [Fintype (sequencesCountedByA052709 n)] :
    (0 < n) ↔ (1 ≤ n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) [Fintype (sequencesCountedByA052709 n)] :
    (0 < n) ↔ (1 ≤ n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) [Fintype (sequencesCountedByA052709 n)] :
    (0 < n) ↔ (1 ≤ n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) [Fintype (sequencesCountedByA052709 n)] :
    (0 < n) ↔ (1 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) [Fintype (sequencesCountedByA052709 n)] :
    (0 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) [Fintype (sequencesCountedByA052709 n)] :
    (0 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) →
    (∀ (n : ℕ) (hn : 1 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) →
    (∀ (n : ℕ) (hn : 1 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) →
    (∀ (n : ℕ) (hn : 1 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) →
    (∀ (n : ℕ) (hn : 1 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) →
    (∀ (n : ℕ) (hn : 1 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) →
    (∀ (n : ℕ) (hn : 1 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) →
    (∀ (n : ℕ) (hn : 1 < n) [Fintype (sequencesCountedByA052709 n)], a n = Fintype.card (sequencesCountedByA052709 n)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) [Fintype (sequencesCountedByA052709 n)]  :
    (0 < n) ↔ (1 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) [Fintype (sequencesCountedByA052709 n)]  :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) [Fintype (sequencesCountedByA052709 n)]  :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) [Fintype (sequencesCountedByA052709 n)]  :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) [Fintype (sequencesCountedByA052709 n)]  :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) [Fintype (sequencesCountedByA052709 n)]  :
    (0 < n) ↔ (1 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) [Fintype (sequencesCountedByA052709 n)]  :
    (0 < n) ↔ (1 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((0 < n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((0 < n) ↔ (1 < n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((0 < n) ↔ (1 < n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((0 < n) ↔ (1 < n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((0 < n) ↔ (1 < n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n : ℕ) [Fintype (sequencesCountedByA052709 n)] (hn : 0 < n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) [Fintype (sequencesCountedByA052709 n)] (hn : 0 < n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) [Fintype (sequencesCountedByA052709 n)] (hn : 0 < n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) [Fintype (sequencesCountedByA052709 n)] (hn : 0 < n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) [Fintype (sequencesCountedByA052709 n)] (hn : 0 < n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
