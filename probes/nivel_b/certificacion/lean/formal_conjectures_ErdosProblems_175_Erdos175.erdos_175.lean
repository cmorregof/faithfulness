import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 175

*References:*
- [erdosproblems.com/175](https://www.erdosproblems.com/175)
- [Sa85] A. Sárközy, *On divisors of binomial coefficients, I*, J. Number Theory 20
  (1985), 70–80.
- [GrRa96] A. Granville and O. Ramaré, *Explicit bounds on exponential sums and the scarcity
  of squarefree binomial coefficients*, Mathematika 43 (1996), 73–107.
- [Ve95] G. Velammal, *Is the binomial coefficient $\binom{2n}{n}$ square free?*,
  Hardy-Ramanujan Journal 18 (1995), 23–45.

Sárközy proved the assertion for all sufficiently large `n`; Granville--Ramaré and Velammal
independently proved the full range `n ≥ 5`.
-/

section

namespace Erdos175

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 5 < n), ¬ Squarefree ((2 * n).choose n)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) →
    (∀ (n : ℕ) (hn : 5 < n), ¬ Squarefree ((2 * n).choose n)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) →
    (∀ (n : ℕ) (hn : 5 < n), ¬ Squarefree ((2 * n).choose n)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) →
    (∀ (n : ℕ) (hn : 5 < n), ¬ Squarefree ((2 * n).choose n)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) →
    (∀ (n : ℕ) (hn : 5 < n), ¬ Squarefree ((2 * n).choose n)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) →
    (∀ (n : ℕ) (hn : 5 < n), ¬ Squarefree ((2 * n).choose n)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) →
    (∀ (n : ℕ) (hn : 5 < n), ¬ Squarefree ((2 * n).choose n)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) →
    (∀ (n : ℕ) (hn : 5 < n), ¬ Squarefree ((2 * n).choose n)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (5 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (5 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (5 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (5 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (5 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (5 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (5 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (5 < n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (5 < n))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (5 < n))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (5 < n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (5 < n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (5 < n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (5 < n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (5 < n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (5 < n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (5 < n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (5 < n)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (5 < n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (5 < n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (5 < n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (5 < n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (5 < n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 6 ≤ n), ¬ Squarefree ((2 * n).choose n)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) →
    (∀ (n : ℕ) (hn : 6 ≤ n), ¬ Squarefree ((2 * n).choose n)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) →
    (∀ (n : ℕ) (hn : 6 ≤ n), ¬ Squarefree ((2 * n).choose n)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) →
    (∀ (n : ℕ) (hn : 6 ≤ n), ¬ Squarefree ((2 * n).choose n)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) →
    (∀ (n : ℕ) (hn : 6 ≤ n), ¬ Squarefree ((2 * n).choose n)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) →
    (∀ (n : ℕ) (hn : 6 ≤ n), ¬ Squarefree ((2 * n).choose n)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) →
    (∀ (n : ℕ) (hn : 6 ≤ n), ¬ Squarefree ((2 * n).choose n)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) →
    (∀ (n : ℕ) (hn : 6 ≤ n), ¬ Squarefree ((2 * n).choose n)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (6 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (6 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (6 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (6 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (6 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (6 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (6 ≤ n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (6 ≤ n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (6 ≤ n))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (6 ≤ n))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (6 ≤ n))) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (6 ≤ n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (6 ≤ n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (6 ≤ n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (6 ≤ n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (6 ≤ n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (6 ≤ n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (6 ≤ n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (6 ≤ n)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (6 ≤ n)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (6 ≤ n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (6 ≤ n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (6 ≤ n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (6 ≤ n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (6 ≤ n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 5), ¬ Squarefree ((2 * n).choose n)

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (n ≥ 5) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (n ≥ 5) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (n ≥ 5) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (n ≥ 5) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (n ≥ 5) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (n ≥ 5) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (n ≥ 5) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (n ≥ 5) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) ↔
    (∀ (n : ℕ) (hn : n ≥ 5), ¬ Squarefree ((2 * n).choose n)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) ↔
    (∀ (n : ℕ) (hn : n ≥ 5), ¬ Squarefree ((2 * n).choose n)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) ↔
    (∀ (n : ℕ) (hn : n ≥ 5), ¬ Squarefree ((2 * n).choose n)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) ↔
    (∀ (n : ℕ) (hn : n ≥ 5), ¬ Squarefree ((2 * n).choose n)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn₀ : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) ↔
    (∀ (n : ℕ) (hn₀ : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) ↔
    (∀ (n : ℕ) (hn₀ : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) ↔
    (∀ (n : ℕ) (hn₀ : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) ↔
    (∀ (n : ℕ) (hn₀ : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : ¬(n < 5)), ¬ Squarefree ((2 * n).choose n)

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (¬(n < 5)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (¬(n < 5)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (¬(n < 5)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (¬(n < 5)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (¬(n < 5)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (¬(n < 5)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (¬(n < 5)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (¬(n < 5)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) ↔
    (∀ (n : ℕ) (hn : ¬(n < 5)), ¬ Squarefree ((2 * n).choose n)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) ↔
    (∀ (n : ℕ) (hn : ¬(n < 5)), ¬ Squarefree ((2 * n).choose n)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) ↔
    (∀ (n : ℕ) (hn : ¬(n < 5)), ¬ Squarefree ((2 * n).choose n)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) ↔
    (∀ (n : ℕ) (hn : ¬(n < 5)), ¬ Squarefree ((2 * n).choose n)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 4 < n), ¬ Squarefree ((2 * n).choose n)

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (4 < n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (4 < n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (4 < n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (4 < n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (4 < n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (4 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (4 < n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (4 < n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) ↔
    (∀ (n : ℕ) (hn : 4 < n), ¬ Squarefree ((2 * n).choose n)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) ↔
    (∀ (n : ℕ) (hn : 4 < n), ¬ Squarefree ((2 * n).choose n)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) ↔
    (∀ (n : ℕ) (hn : 4 < n), ¬ Squarefree ((2 * n).choose n)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) ↔
    (∀ (n : ℕ) (hn : 4 < n), ¬ Squarefree ((2 * n).choose n)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 5), ¬ Squarefree ((2 * n).choose n)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) →
    (∀ (n : ℕ) (hn : n > 5), ¬ Squarefree ((2 * n).choose n)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) →
    (∀ (n : ℕ) (hn : n > 5), ¬ Squarefree ((2 * n).choose n)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) →
    (∀ (n : ℕ) (hn : n > 5), ¬ Squarefree ((2 * n).choose n)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) →
    (∀ (n : ℕ) (hn : n > 5), ¬ Squarefree ((2 * n).choose n)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) →
    (∀ (n : ℕ) (hn : n > 5), ¬ Squarefree ((2 * n).choose n)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) →
    (∀ (n : ℕ) (hn : n > 5), ¬ Squarefree ((2 * n).choose n)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) →
    (∀ (n : ℕ) (hn : n > 5), ¬ Squarefree ((2 * n).choose n)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (n > 5) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (n > 5) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (n > 5) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (n > 5) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (n > 5) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (n > 5) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (n > 5) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (n > 5))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (n > 5))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (n > 5))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (n > 5))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (n > 5))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (n > 5))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (n > 5))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (n > 5))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (n > 5)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (n > 5)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (n > 5)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (n > 5)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (n > 5)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (n > 5)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (n > 5)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (n > 5)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 6), ¬ Squarefree ((2 * n).choose n)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) →
    (∀ (n : ℕ) (hn : n ≥ 6), ¬ Squarefree ((2 * n).choose n)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) →
    (∀ (n : ℕ) (hn : n ≥ 6), ¬ Squarefree ((2 * n).choose n)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) →
    (∀ (n : ℕ) (hn : n ≥ 6), ¬ Squarefree ((2 * n).choose n)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) →
    (∀ (n : ℕ) (hn : n ≥ 6), ¬ Squarefree ((2 * n).choose n)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) →
    (∀ (n : ℕ) (hn : n ≥ 6), ¬ Squarefree ((2 * n).choose n)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) →
    (∀ (n : ℕ) (hn : n ≥ 6), ¬ Squarefree ((2 * n).choose n)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) →
    (∀ (n : ℕ) (hn : n ≥ 6), ¬ Squarefree ((2 * n).choose n)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (n ≥ 6) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (n ≥ 6) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (n ≥ 6) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (n ≥ 6) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (n ≥ 6) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (n ≥ 6) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (n ≥ 6) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (n ≥ 6))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (n ≥ 6))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (n ≥ 6))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (n ≥ 6))) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (n ≥ 6))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (n ≥ 6))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (n ≥ 6))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (n ≥ 6))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (n ≥ 6))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (n ≥ 6)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (n ≥ 6)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (n ≥ 6)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (n ≥ 6)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (n ≥ 6)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (n ≥ 6)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (n ≥ 6)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (n ≥ 6)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (n ≥ 6)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 4 ≤ n), ¬ Squarefree ((2 * n).choose n)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n), ¬ Squarefree ((2 * n).choose n)) →
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n), ¬ Squarefree ((2 * n).choose n)) →
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n), ¬ Squarefree ((2 * n).choose n)) →
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n), ¬ Squarefree ((2 * n).choose n)) →
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n), ¬ Squarefree ((2 * n).choose n)) →
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n), ¬ Squarefree ((2 * n).choose n)) →
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n), ¬ Squarefree ((2 * n).choose n)) →
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (4 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (4 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (4 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (4 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (4 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (4 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (4 ≤ n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 4 < n), ¬ Squarefree ((3 * n).choose n)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 < n), ¬ Squarefree ((3 * n).choose n)) →
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 < n), ¬ Squarefree ((3 * n).choose n)) →
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 < n), ¬ Squarefree ((3 * n).choose n)) →
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 < n), ¬ Squarefree ((3 * n).choose n)) →
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 < n), ¬ Squarefree ((3 * n).choose n)) →
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 < n), ¬ Squarefree ((3 * n).choose n)) →
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 < n), ¬ Squarefree ((3 * n).choose n)) →
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) →
    (∀ (n : ℕ) (hn : 4 < n), ¬ Squarefree ((3 * n).choose n)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) →
    (∀ (n : ℕ) (hn : 4 < n), ¬ Squarefree ((3 * n).choose n)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) →
    (∀ (n : ℕ) (hn : 4 < n), ¬ Squarefree ((3 * n).choose n)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) →
    (∀ (n : ℕ) (hn : 4 < n), ¬ Squarefree ((3 * n).choose n)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) →
    (∀ (n : ℕ) (hn : 4 < n), ¬ Squarefree ((3 * n).choose n)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) →
    (∀ (n : ℕ) (hn : 4 < n), ¬ Squarefree ((3 * n).choose n)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ¬ Squarefree ((2 * n).choose n)) →
    (∀ (n : ℕ) (hn : 4 < n), ¬ Squarefree ((3 * n).choose n)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (5 ≤ n) ∧ (¬(¬ Squarefree ((3 * n).choose n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (5 ≤ n) ∧ (¬(¬ Squarefree ((3 * n).choose n))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (5 ≤ n) ∧ (¬(¬ Squarefree ((3 * n).choose n))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (5 ≤ n) ∧ (¬(¬ Squarefree ((3 * n).choose n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (5 ≤ n) ∧ (¬(¬ Squarefree ((3 * n).choose n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (5 ≤ n) ∧ (¬(¬ Squarefree ((3 * n).choose n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (5 ≤ n) ∧ (¬(¬ Squarefree ((3 * n).choose n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (5 ≤ n) ∧ (¬(¬ Squarefree ((3 * n).choose n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((¬ Squarefree ((2 * n).choose n)) ↔ (¬ Squarefree ((3 * n).choose n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((¬ Squarefree ((2 * n).choose n)) ↔ (¬ Squarefree ((3 * n).choose n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((¬ Squarefree ((2 * n).choose n)) ↔ (¬ Squarefree ((3 * n).choose n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((¬ Squarefree ((2 * n).choose n)) ↔ (¬ Squarefree ((3 * n).choose n))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((¬ Squarefree ((2 * n).choose n)) ↔ (¬ Squarefree ((3 * n).choose n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((¬ Squarefree ((2 * n).choose n)) ↔ (¬ Squarefree ((3 * n).choose n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((¬ Squarefree ((2 * n).choose n)) ↔ (¬ Squarefree ((3 * n).choose n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 5 ≤ n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 5 ≤ n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 5 ≤ n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 5 ≤ n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 5 ≤ n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
