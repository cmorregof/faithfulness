import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 294

*References:*
- [erdosproblems.com/294](https://www.erdosproblems.com/294)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [LiSa24] Liu, Y. and Sawhney, M., *On further questions regarding unit fractions*.
  [arXiv:2404.07113](https://arxiv.org/abs/2404.07113) (2024).
-/

section

open Filter

namespace Erdos294

/-- `HasUnitFractionSolution m N` says that $1=\frac{1}{n_1}+\cdots+\frac{1}{n_k}$ for some
integers $m=n_1<\cdots<n_k\leq N$: the $n_i$ form a finite set `s` whose least element is `m`. -/
def HasUnitFractionSolution (m N : ℕ) : Prop :=
  ∃ s : Finset ℕ, m ∈ s ∧ (∀ n ∈ s, m ≤ n ∧ n ≤ N) ∧ ∑ n ∈ s, (1 : ℚ) / n = 1

/-- $t(N)$: the least positive integer $t$ such that there is no solution to
$1=\frac{1}{n_1}+\cdots+\frac{1}{n_k}$ with $t=n_1<\cdots<n_k\leq N$. The set of candidates
contains $N+1$, so `sInf` is a true minimum. -/
noncomputable def t (N : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ ¬ HasUnitFractionSolution m N}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} (hN : 1 ≤ N), HasUnitFractionSolution 1 N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} (hN : 1 < N), HasUnitFractionSolution 1 N

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), HasUnitFractionSolution 1 N) →
    (∀ {N : ℕ} (hN : 1 < N), HasUnitFractionSolution 1 N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), HasUnitFractionSolution 1 N) →
    (∀ {N : ℕ} (hN : 1 < N), HasUnitFractionSolution 1 N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), HasUnitFractionSolution 1 N) →
    (∀ {N : ℕ} (hN : 1 < N), HasUnitFractionSolution 1 N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), HasUnitFractionSolution 1 N) →
    (∀ {N : ℕ} (hN : 1 < N), HasUnitFractionSolution 1 N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), HasUnitFractionSolution 1 N) →
    (∀ {N : ℕ} (hN : 1 < N), HasUnitFractionSolution 1 N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), HasUnitFractionSolution 1 N) →
    (∀ {N : ℕ} (hN : 1 < N), HasUnitFractionSolution 1 N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), HasUnitFractionSolution 1 N) →
    (∀ {N : ℕ} (hN : 1 < N), HasUnitFractionSolution 1 N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {N : ℕ}  :
    (1 ≤ N) ↔ (1 < N) := by
  omega

set_option maxHeartbeats 200000 in
example {N : ℕ}  :
    (1 ≤ N) ↔ (1 < N) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {N : ℕ}  :
    (1 ≤ N) ↔ (1 < N) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {N : ℕ}  :
    (1 ≤ N) ↔ (1 < N) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {N : ℕ}  :
    (1 ≤ N) ↔ (1 < N) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {N : ℕ}  :
    (1 ≤ N) ↔ (1 < N) := by
  simp_all

set_option maxHeartbeats 200000 in
example {N : ℕ}  :
    (1 ≤ N) ↔ (1 < N) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((1 ≤ N) ↔ (1 < N))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((1 ≤ N) ↔ (1 < N))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((1 ≤ N) ↔ (1 < N))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((1 ≤ N) ↔ (1 < N))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((1 ≤ N) ↔ (1 < N))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((1 ≤ N) ↔ (1 < N))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ N) ↔ (1 < N)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ N) ↔ (1 < N)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ N) ↔ (1 < N)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ N) ↔ (1 < N)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ N) ↔ (1 < N)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ N) ↔ (1 < N)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} (hN : 1 ≤ N), HasUnitFractionSolution 1 N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} (hN : N ≥ 1), HasUnitFractionSolution 1 N

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (N ≥ 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (N ≥ 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (N ≥ 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (N ≥ 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (N ≥ 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (N ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (N ≥ 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (N ≥ 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), HasUnitFractionSolution 1 N) ↔
    (∀ {N : ℕ} (hN : N ≥ 1), HasUnitFractionSolution 1 N) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), HasUnitFractionSolution 1 N) ↔
    (∀ {N : ℕ} (hN : N ≥ 1), HasUnitFractionSolution 1 N) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), HasUnitFractionSolution 1 N) ↔
    (∀ {N : ℕ} (hN : N ≥ 1), HasUnitFractionSolution 1 N) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), HasUnitFractionSolution 1 N) ↔
    (∀ {N : ℕ} (hN : N ≥ 1), HasUnitFractionSolution 1 N) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} (hN : 1 ≤ N), HasUnitFractionSolution 1 N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} (hN₀ : 1 ≤ N), HasUnitFractionSolution 1 N

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), HasUnitFractionSolution 1 N) ↔
    (∀ {N : ℕ} (hN₀ : 1 ≤ N), HasUnitFractionSolution 1 N) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), HasUnitFractionSolution 1 N) ↔
    (∀ {N : ℕ} (hN₀ : 1 ≤ N), HasUnitFractionSolution 1 N) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), HasUnitFractionSolution 1 N) ↔
    (∀ {N : ℕ} (hN₀ : 1 ≤ N), HasUnitFractionSolution 1 N) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), HasUnitFractionSolution 1 N) ↔
    (∀ {N : ℕ} (hN₀ : 1 ≤ N), HasUnitFractionSolution 1 N) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} (hN : 1 ≤ N), HasUnitFractionSolution 1 N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} (hN : ¬(N < 1)), HasUnitFractionSolution 1 N

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (¬(N < 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (¬(N < 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (¬(N < 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (¬(N < 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (¬(N < 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (¬(N < 1)) := by
  omega

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (¬(N < 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (¬(N < 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), HasUnitFractionSolution 1 N) ↔
    (∀ {N : ℕ} (hN : ¬(N < 1)), HasUnitFractionSolution 1 N) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), HasUnitFractionSolution 1 N) ↔
    (∀ {N : ℕ} (hN : ¬(N < 1)), HasUnitFractionSolution 1 N) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), HasUnitFractionSolution 1 N) ↔
    (∀ {N : ℕ} (hN : ¬(N < 1)), HasUnitFractionSolution 1 N) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), HasUnitFractionSolution 1 N) ↔
    (∀ {N : ℕ} (hN : ¬(N < 1)), HasUnitFractionSolution 1 N) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} (hN : 1 ≤ N), HasUnitFractionSolution 1 N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} (hN : 0 < N), HasUnitFractionSolution 1 N

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (0 < N) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (0 < N) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (0 < N) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (0 < N) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (0 < N) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (0 < N) := by
  omega

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (0 < N) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {N : ℕ} :
    (1 ≤ N) ↔ (0 < N) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), HasUnitFractionSolution 1 N) ↔
    (∀ {N : ℕ} (hN : 0 < N), HasUnitFractionSolution 1 N) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), HasUnitFractionSolution 1 N) ↔
    (∀ {N : ℕ} (hN : 0 < N), HasUnitFractionSolution 1 N) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), HasUnitFractionSolution 1 N) ↔
    (∀ {N : ℕ} (hN : 0 < N), HasUnitFractionSolution 1 N) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), HasUnitFractionSolution 1 N) ↔
    (∀ {N : ℕ} (hN : 0 < N), HasUnitFractionSolution 1 N) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} (hN : 1 ≤ N), HasUnitFractionSolution 1 N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {N : ℕ} (hN : N > 1), HasUnitFractionSolution 1 N

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), HasUnitFractionSolution 1 N) →
    (∀ {N : ℕ} (hN : N > 1), HasUnitFractionSolution 1 N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), HasUnitFractionSolution 1 N) →
    (∀ {N : ℕ} (hN : N > 1), HasUnitFractionSolution 1 N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), HasUnitFractionSolution 1 N) →
    (∀ {N : ℕ} (hN : N > 1), HasUnitFractionSolution 1 N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), HasUnitFractionSolution 1 N) →
    (∀ {N : ℕ} (hN : N > 1), HasUnitFractionSolution 1 N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), HasUnitFractionSolution 1 N) →
    (∀ {N : ℕ} (hN : N > 1), HasUnitFractionSolution 1 N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), HasUnitFractionSolution 1 N) →
    (∀ {N : ℕ} (hN : N > 1), HasUnitFractionSolution 1 N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {N : ℕ} (hN : 1 ≤ N), HasUnitFractionSolution 1 N) →
    (∀ {N : ℕ} (hN : N > 1), HasUnitFractionSolution 1 N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {N : ℕ}  :
    (1 ≤ N) ↔ (N > 1) := by
  omega

set_option maxHeartbeats 200000 in
example {N : ℕ}  :
    (1 ≤ N) ↔ (N > 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {N : ℕ}  :
    (1 ≤ N) ↔ (N > 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {N : ℕ}  :
    (1 ≤ N) ↔ (N > 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {N : ℕ}  :
    (1 ≤ N) ↔ (N > 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {N : ℕ}  :
    (1 ≤ N) ↔ (N > 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example {N : ℕ}  :
    (1 ≤ N) ↔ (N > 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((1 ≤ N) ↔ (N > 1))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((1 ≤ N) ↔ (N > 1))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((1 ≤ N) ↔ (N > 1))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((1 ≤ N) ↔ (N > 1))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((1 ≤ N) ↔ (N > 1))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((1 ≤ N) ↔ (N > 1))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ N) ↔ (N > 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ N) ↔ (N > 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ N) ↔ (N > 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ N) ↔ (N > 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ N) ↔ (N > 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ N) ↔ (N > 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {N : ℕ} (hN : 1 ≤ N) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {N : ℕ} (hN : 1 ≤ N) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {N : ℕ} (hN : 1 ≤ N) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {N : ℕ} (hN : 1 ≤ N) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {N : ℕ} (hN : 1 ≤ N) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
