import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Denominators of $\sum_{k=1}^n \frac{1}{k 2^k}$

$a(n)$ is the denominator of the sum
$$\sum_{i=1}^n \frac{1}{i} \binom{2n-i-1}{i-1}$$

*References:*
- [A175386](https://oeis.org/A175386)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/

section

namespace OeisA175386

/--
$a(n)$ is the denominator of the sum
$$\sum_{i=1}^n \frac{1}{i} \binom{2n-i-1}{i-1}$$
-/
def a (n : ℕ) : ℕ :=
  (Finset.sum (Finset.Icc 1 n) fun i : ℕ =>
    -- The upper index is $2n - i - 1$, which is equivalent to
    -- $2n - (i+1)$ in $\mathbb{N}$ for $i \le n$.
    -- The lower index $i-1$ is standard subtraction in $\mathbb{N}$.
    let num : ℕ := Nat.choose (2 * n - (i + 1)) (i - 1)
    (num : ℚ) / (i : ℚ)
  ).den

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n), a n ≠ 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), a n ≠ 1

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≠ 1) →
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≠ 1) →
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≠ 1) →
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≠ 1) →
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≠ 1) →
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≠ 1) →
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n ≠ 1) →
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 < n) ↔ (1 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 < n) ↔ (1 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 < n) ↔ (1 ≤ n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (1 ≤ n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (1 ≤ n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (1 ≤ n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (1 ≤ n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (1 ≤ n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (1 ≤ n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (1 ≤ n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (1 ≤ n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (1 ≤ n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (1 ≤ n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (1 ≤ n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (1 ≤ n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n), a n ≠ 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 1), a n ≠ 1

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (n > 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (n > 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (n > 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (n > 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (n > 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (n > 1) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (n > 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (n > 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) ↔
    (∀ (n : ℕ) (hn : n > 1), a n ≠ 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) ↔
    (∀ (n : ℕ) (hn : n > 1), a n ≠ 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) ↔
    (∀ (n : ℕ) (hn : n > 1), a n ≠ 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) ↔
    (∀ (n : ℕ) (hn : n > 1), a n ≠ 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n), a n ≠ 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n), ¬(a n = 1)

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (a n ≠ 1) ↔ (¬(a n = 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (a n ≠ 1) ↔ (¬(a n = 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (a n ≠ 1) ↔ (¬(a n = 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (a n ≠ 1) ↔ (¬(a n = 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (a n ≠ 1) ↔ (¬(a n = 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (a n ≠ 1) ↔ (¬(a n = 1)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (a n ≠ 1) ↔ (¬(a n = 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (a n ≠ 1) ↔ (¬(a n = 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) ↔
    (∀ (n : ℕ) (hn : 1 < n), ¬(a n = 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) ↔
    (∀ (n : ℕ) (hn : 1 < n), ¬(a n = 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) ↔
    (∀ (n : ℕ) (hn : 1 < n), ¬(a n = 1)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) ↔
    (∀ (n : ℕ) (hn : 1 < n), ¬(a n = 1)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n), a n ≠ 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn₀ : 1 < n), a n ≠ 1

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) ↔
    (∀ (n : ℕ) (hn₀ : 1 < n), a n ≠ 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) ↔
    (∀ (n : ℕ) (hn₀ : 1 < n), a n ≠ 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) ↔
    (∀ (n : ℕ) (hn₀ : 1 < n), a n ≠ 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) ↔
    (∀ (n : ℕ) (hn₀ : 1 < n), a n ≠ 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n), a n ≠ 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : ¬(n ≤ 1)), a n ≠ 1

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 1)), a n ≠ 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 1)), a n ≠ 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 1)), a n ≠ 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 1)), a n ≠ 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n), a n ≠ 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), a n ≠ 1

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (2 ≤ n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (2 ≤ n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (2 ≤ n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (2 ≤ n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (2 ≤ n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (2 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) ↔
    (∀ (n : ℕ) (hn : 2 ≤ n), a n ≠ 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) ↔
    (∀ (n : ℕ) (hn : 2 ≤ n), a n ≠ 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) ↔
    (∀ (n : ℕ) (hn : 2 ≤ n), a n ≠ 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) ↔
    (∀ (n : ℕ) (hn : 2 ≤ n), a n ≠ 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n), a n ≠ 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 1), a n ≠ 1

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), a n ≠ 1) →
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), a n ≠ 1) →
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), a n ≠ 1) →
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), a n ≠ 1) →
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), a n ≠ 1) →
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), a n ≠ 1) →
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), a n ≠ 1) →
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 < n) ↔ (n ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 < n) ↔ (n ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 < n) ↔ (n ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 < n) ↔ (n ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 < n) ↔ (n ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 < n) ↔ (n ≥ 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 < n) ↔ (n ≥ 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (n ≥ 1))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (n ≥ 1))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (n ≥ 1))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (n ≥ 1))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (n ≥ 1))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (n ≥ 1))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (n ≥ 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (n ≥ 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (n ≥ 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (n ≥ 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (n ≥ 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (n ≥ 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n), a n ≠ 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 < n), a n ≠ 1

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) →
    (∀ (n : ℕ) (hn : 2 < n), a n ≠ 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) →
    (∀ (n : ℕ) (hn : 2 < n), a n ≠ 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) →
    (∀ (n : ℕ) (hn : 2 < n), a n ≠ 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) →
    (∀ (n : ℕ) (hn : 2 < n), a n ≠ 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) →
    (∀ (n : ℕ) (hn : 2 < n), a n ≠ 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) →
    (∀ (n : ℕ) (hn : 2 < n), a n ≠ 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) →
    (∀ (n : ℕ) (hn : 2 < n), a n ≠ 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 < n) ↔ (2 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 < n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 < n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 < n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 < n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 < n) ↔ (2 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 < n) ↔ (2 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (2 < n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (2 < n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (2 < n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (2 < n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (2 < n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (2 < n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (2 < n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (2 < n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (2 < n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (2 < n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (2 < n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (2 < n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n), a n ≠ 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), a n ≠ 1

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) →
    (∀ (n : ℕ) (hn : 3 ≤ n), a n ≠ 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) →
    (∀ (n : ℕ) (hn : 3 ≤ n), a n ≠ 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) →
    (∀ (n : ℕ) (hn : 3 ≤ n), a n ≠ 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) →
    (∀ (n : ℕ) (hn : 3 ≤ n), a n ≠ 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) →
    (∀ (n : ℕ) (hn : 3 ≤ n), a n ≠ 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) →
    (∀ (n : ℕ) (hn : 3 ≤ n), a n ≠ 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), a n ≠ 1) →
    (∀ (n : ℕ) (hn : 3 ≤ n), a n ≠ 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 < n) ↔ (3 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 < n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 < n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 < n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 < n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 < n) ↔ (3 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 < n) ↔ (3 ≤ n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (3 ≤ n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (3 ≤ n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (3 ≤ n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (3 ≤ n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (3 ≤ n))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (3 ≤ n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (3 ≤ n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (3 ≤ n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (3 ≤ n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (3 ≤ n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (3 ≤ n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (3 ≤ n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (3 ≤ n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (3 ≤ n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 < n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 < n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 < n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 < n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 < n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
