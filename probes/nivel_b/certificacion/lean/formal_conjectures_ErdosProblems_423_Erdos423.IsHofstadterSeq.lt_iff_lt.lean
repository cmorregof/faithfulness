import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 423

*References:*
- [erdosproblems.com/423](https://www.erdosproblems.com/423)
- [Er77c] Erdős, P., *Problems and results on combinatorial number theory. III*,
  Number theory day (Proc. Conf., Rockefeller Univ., New York, 1976), 1977, pp. 43–72.
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial
  number theory*, Monographies de L'Enseignement Mathématique (1980).
- [Cu25] Cushman, A., *A Note on the Sum-Product Problem and the Convex Sumset Problem*.
  arXiv:2512.13849 (2025).
- [Ta26] Tang, Q., *The Hofstadter consecutive-sum sequence omits infinitely many positive
  integers*. arXiv:2603.09939 (2026).
- [Bolan] Bolan, M., *Hofstader–Ulam Sequence*,
  https://github.com/mjtb49/HofstaderUlam/blob/main/HofstaderUlamSequence.pdf
- [OEIS A005243](https://oeis.org/A005243)
-/

section

open Finset BigOperators Filter Asymptotics

namespace Erdos423

/-- `IsConsecutiveBlockSum a k m` means that $m$ equals the sum of at least two
    consecutive terms of the sequence $a$, using indices from $\{1, \ldots, k - 1\}$.
    That is, there exist $i, j$ with $1 \le i$, $i + 1 \le j$, $j \le k - 1$ such that
    $m = a(i) + a(i+1) + \cdots + a(j)$. -/
def IsConsecutiveBlockSum (a : ℕ → ℕ) (k : ℕ) (m : ℕ) : Prop :=
  ∃ i j : ℕ, 1 ≤ i ∧ i + 1 ≤ j ∧ j + 1 ≤ k ∧
    m = ∑ l ∈ Finset.Icc i j, a l

/-- The Hofstadter sequence (OEIS A005243): $a(1) = 1$, $a(2) = 2$, and for $k \ge 3$,
$a(k)$ is the least integer $> a(k-1)$ that equals the sum of at least two consecutive terms from
$\{a(1), \ldots, a(k-1)\}$. The sequence begins $1, 2, 3, 5, 6, 8, 10, 11, \ldots$. -/
def IsHofstadterSeq (a : ℕ → ℕ) : Prop :=
  a 1 = 1 ∧ a 2 = 2 ∧
  ∀ k : ℕ, 3 ≤ k →
    IsConsecutiveBlockSum a k (a k) ∧
    a (k - 1) < a k ∧
    ∀ m : ℕ, a (k - 1) < m → m < a k → ¬IsConsecutiveBlockSum a k m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hj : 1 ≤ j), a i < a j ↔ i < j

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hj : 1 ≤ j), a i < a j ↔ i < j) →
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hj : 1 ≤ j), a i < a j ↔ i < j) →
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hj : 1 ≤ j), a i < a j ↔ i < j) →
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hj : 1 ≤ j), a i < a j ↔ i < j) →
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hj : 1 ≤ j), a i < a j ↔ i < j) →
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hj : 1 ≤ j), a i < a j ↔ i < j) →
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hj : 1 ≤ j), a i < a j ↔ i < j) →
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hj : 1 ≤ j) :
    (1 ≤ i) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hj : 1 ≤ j) :
    (1 ≤ i) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hj : 1 ≤ j) :
    (1 ≤ i) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hj : 1 ≤ j) :
    (1 ≤ i) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hj : 1 ≤ j) :
    (1 ≤ i) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hj : 1 ≤ j) :
    (1 ≤ i) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hj : 1 ≤ j) :
    (1 ≤ i) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ), ¬((1 ≤ i) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ), ¬((1 ≤ i) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ), ¬((1 ≤ i) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ), ¬((1 ≤ i) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ), ¬((1 ≤ i) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ), ¬((1 ≤ i) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 < i) (hj : 1 ≤ j), a i < a j ↔ i < j

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) →
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 < i) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) →
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 < i) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) →
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 < i) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) →
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 < i) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) →
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 < i) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) →
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 < i) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) →
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 < i) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hj : 1 ≤ j) :
    (1 ≤ i) ↔ (1 < i) := by
  omega

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hj : 1 ≤ j) :
    (1 ≤ i) ↔ (1 < i) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hj : 1 ≤ j) :
    (1 ≤ i) ↔ (1 < i) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hj : 1 ≤ j) :
    (1 ≤ i) ↔ (1 < i) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hj : 1 ≤ j) :
    (1 ≤ i) ↔ (1 < i) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hj : 1 ≤ j) :
    (1 ≤ i) ↔ (1 < i) := by
  simp_all

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hj : 1 ≤ j) :
    (1 ≤ i) ↔ (1 < i) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ), ¬((1 ≤ i) ↔ (1 < i)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ), ¬((1 ≤ i) ↔ (1 < i)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ), ¬((1 ≤ i) ↔ (1 < i)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ), ¬((1 ≤ i) ↔ (1 < i)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ), ¬((1 ≤ i) ↔ (1 < i)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ), ¬((1 ≤ i) ↔ (1 < i)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : i ≥ 1) (hj : 1 ≤ j), a i < a j ↔ i < j

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} :
    (1 ≤ i) ↔ (i ≥ 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} :
    (1 ≤ i) ↔ (i ≥ 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} :
    (1 ≤ i) ↔ (i ≥ 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} :
    (1 ≤ i) ↔ (i ≥ 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} :
    (1 ≤ i) ↔ (i ≥ 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} :
    (1 ≤ i) ↔ (i ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} :
    (1 ≤ i) ↔ (i ≥ 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} :
    (1 ≤ i) ↔ (i ≥ 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) ↔
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : i ≥ 1) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) ↔
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : i ≥ 1) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) ↔
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : i ≥ 1) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) ↔
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : i ≥ 1) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hj : 1 ≤ j) (hi : 1 ≤ i), a i < a j ↔ i < j

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) ↔
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hj : 1 ≤ j) (hi : 1 ≤ i), a i < a j ↔ i < j) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) ↔
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hj : 1 ≤ j) (hi : 1 ≤ i), a i < a j ↔ i < j) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) ↔
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hj : 1 ≤ j) (hi : 1 ≤ i), a i < a j ↔ i < j) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) ↔
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hj : 1 ≤ j) (hi : 1 ≤ i), a i < a j ↔ i < j) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a : ℕ → ℕ} (ha₀ : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) ↔
    (∀ {a : ℕ → ℕ} (ha₀ : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) ↔
    (∀ {a : ℕ → ℕ} (ha₀ : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) ↔
    (∀ {a : ℕ → ℕ} (ha₀ : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) ↔
    (∀ {a : ℕ → ℕ} (ha₀ : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : ¬(i < 1)) (hj : 1 ≤ j), a i < a j ↔ i < j

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} :
    (1 ≤ i) ↔ (¬(i < 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} :
    (1 ≤ i) ↔ (¬(i < 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} :
    (1 ≤ i) ↔ (¬(i < 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} :
    (1 ≤ i) ↔ (¬(i < 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} :
    (1 ≤ i) ↔ (¬(i < 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} :
    (1 ≤ i) ↔ (¬(i < 1)) := by
  omega

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} :
    (1 ≤ i) ↔ (¬(i < 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} :
    (1 ≤ i) ↔ (¬(i < 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) ↔
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : ¬(i < 1)) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) ↔
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : ¬(i < 1)) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) ↔
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : ¬(i < 1)) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) ↔
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : ¬(i < 1)) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 0 < i) (hj : 1 ≤ j), a i < a j ↔ i < j

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} :
    (1 ≤ i) ↔ (0 < i) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} :
    (1 ≤ i) ↔ (0 < i) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} :
    (1 ≤ i) ↔ (0 < i) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} :
    (1 ≤ i) ↔ (0 < i) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} :
    (1 ≤ i) ↔ (0 < i) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} :
    (1 ≤ i) ↔ (0 < i) := by
  omega

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} :
    (1 ≤ i) ↔ (0 < i) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} :
    (1 ≤ i) ↔ (0 < i) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) ↔
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 0 < i) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) ↔
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 0 < i) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) ↔
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 0 < i) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) ↔
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 0 < i) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : i > 1) (hj : 1 ≤ j), a i < a j ↔ i < j

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) →
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : i > 1) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) →
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : i > 1) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) →
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : i > 1) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) →
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : i > 1) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) →
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : i > 1) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) →
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : i > 1) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) →
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : i > 1) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hj : 1 ≤ j) :
    (1 ≤ i) ↔ (i > 1) := by
  omega

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hj : 1 ≤ j) :
    (1 ≤ i) ↔ (i > 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hj : 1 ≤ j) :
    (1 ≤ i) ↔ (i > 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hj : 1 ≤ j) :
    (1 ≤ i) ↔ (i > 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hj : 1 ≤ j) :
    (1 ≤ i) ↔ (i > 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hj : 1 ≤ j) :
    (1 ≤ i) ↔ (i > 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hj : 1 ≤ j) :
    (1 ≤ i) ↔ (i > 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ), ¬((1 ≤ i) ↔ (i > 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ), ¬((1 ≤ i) ↔ (i > 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ), ¬((1 ≤ i) ↔ (i > 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ), ¬((1 ≤ i) ↔ (i > 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ), ¬((1 ≤ i) ↔ (i > 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (i : ℕ), ¬((1 ≤ i) ↔ (i > 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 0 < i) (hj : 1 < j), a i < a j ↔ i < j

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) →
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 0 < i) (hj : 1 < j), a i < a j ↔ i < j) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) →
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 0 < i) (hj : 1 < j), a i < a j ↔ i < j) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) →
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 0 < i) (hj : 1 < j), a i < a j ↔ i < j) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) →
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 0 < i) (hj : 1 < j), a i < a j ↔ i < j) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) →
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 0 < i) (hj : 1 < j), a i < a j ↔ i < j) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) →
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 0 < i) (hj : 1 < j), a i < a j ↔ i < j) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) →
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 0 < i) (hj : 1 < j), a i < a j ↔ i < j) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hi : 1 ≤ i) :
    (1 ≤ j) ↔ (1 < j) := by
  omega

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hi : 1 ≤ i) :
    (1 ≤ j) ↔ (1 < j) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hi : 1 ≤ i) :
    (1 ≤ j) ↔ (1 < j) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hi : 1 ≤ i) :
    (1 ≤ j) ↔ (1 < j) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hi : 1 ≤ i) :
    (1 ≤ j) ↔ (1 < j) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hi : 1 ≤ i) :
    (1 ≤ j) ↔ (1 < j) := by
  simp_all

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hi : 1 ≤ i) :
    (1 ≤ j) ↔ (1 < j) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ), ¬((1 ≤ j) ↔ (1 < j)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ), ¬((1 ≤ j) ↔ (1 < j)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ), ¬((1 ≤ j) ↔ (1 < j)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ), ¬((1 ≤ j) ↔ (1 < j)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ), ¬((1 ≤ j) ↔ (1 < j)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ), ¬((1 ≤ j) ↔ (1 < j)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 0 < i), a i < a j ↔ i < j

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 0 < i), a i < a j ↔ i < j) →
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 0 < i), a i < a j ↔ i < j) →
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 0 < i), a i < a j ↔ i < j) →
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 0 < i), a i < a j ↔ i < j) →
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 0 < i), a i < a j ↔ i < j) →
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 0 < i), a i < a j ↔ i < j) →
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 0 < i), a i < a j ↔ i < j) →
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hi : 1 ≤ i) :
    (1 ≤ j) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hi : 1 ≤ i) :
    (1 ≤ j) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hi : 1 ≤ i) :
    (1 ≤ j) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hi : 1 ≤ i) :
    (1 ≤ j) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hi : 1 ≤ i) :
    (1 ≤ j) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hi : 1 ≤ i) :
    (1 ≤ j) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hi : 1 ≤ i) :
    (1 ≤ j) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ), ¬((1 ≤ j) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ), ¬((1 ≤ j) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ), ¬((1 ≤ j) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ), ¬((1 ≤ j) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ), ¬((1 ≤ j) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ), ¬((1 ≤ j) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i), a i < a j ↔ i < j

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i), a i < a j ↔ i < j) →
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i), a i < a j ↔ i < j) →
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i), a i < a j ↔ i < j) →
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i), a i < a j ↔ i < j) →
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i), a i < a j ↔ i < j) →
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i), a i < a j ↔ i < j) →
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i), a i < a j ↔ i < j) →
    (∀ {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j), a i < a j ↔ i < j) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hi : 1 ≤ i) :
    (1 ≤ j) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hi : 1 ≤ i) :
    (1 ≤ j) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hi : 1 ≤ i) :
    (1 ≤ j) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hi : 1 ≤ i) :
    (1 ≤ j) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hi : 1 ≤ i) :
    (1 ≤ j) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hi : 1 ≤ i) :
    (1 ≤ j) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hi : 1 ≤ i) :
    (1 ≤ j) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ), ¬((1 ≤ j) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ), ¬((1 ≤ j) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ), ¬((1 ≤ j) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ), ¬((1 ≤ j) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ), ¬((1 ≤ j) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ), ¬((1 ≤ j) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hi : 1 ≤ i) (hj : 1 ≤ j) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hi : 1 ≤ i) (hj : 1 ≤ j) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hi : 1 ≤ i) (hj : 1 ≤ j) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hi : 1 ≤ i) (hj : 1 ≤ j) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {a : ℕ → ℕ} {i j : ℕ} (ha : IsHofstadterSeq a) (hi : 1 ≤ i) (hj : 1 ≤ j) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
