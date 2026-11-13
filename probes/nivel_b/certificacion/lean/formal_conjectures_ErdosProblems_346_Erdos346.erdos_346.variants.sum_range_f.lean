import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 346

*References:*
 - [erdosproblems.com/346](https://www.erdosproblems.com/346)
 - [Gr64d] Graham, R. L., A property of Fibonacci numbers. Fibonacci Quart. (1964), 1-10.
 - [ErGr80] Erdős, P. and Graham, R., Old and new problems and results in combinatorial number
    theory. Monographies de L'Enseignement Mathematique (1980).
 -
-/

section

open Filter Topology Set

namespace Erdos346

/-- We define a sequence `f` by the formula `f n = n.fib - (- 1) ^ n`. -/
def f (n : ℕ) : ℕ := if Even n then n.fib - 1 else n.fib + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ) (hm : 1 < m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) →
    (∀ (m : ℕ) (hm : 1 < m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) →
    (∀ (m : ℕ) (hm : 1 < m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) →
    (∀ (m : ℕ) (hm : 1 < m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) →
    (∀ (m : ℕ) (hm : 1 < m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) →
    (∀ (m : ℕ) (hm : 1 < m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) →
    (∀ (m : ℕ) (hm : 1 < m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) →
    (∀ (m : ℕ) (hm : 1 < m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (m : ℕ)  :
    (1 ≤ m) ↔ (1 < m) := by
  omega

set_option maxHeartbeats 200000 in
example (m : ℕ)  :
    (1 ≤ m) ↔ (1 < m) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (m : ℕ)  :
    (1 ≤ m) ↔ (1 < m) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (m : ℕ)  :
    (1 ≤ m) ↔ (1 < m) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (m : ℕ)  :
    (1 ≤ m) ↔ (1 < m) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (m : ℕ)  :
    (1 ≤ m) ↔ (1 < m) := by
  simp_all

set_option maxHeartbeats 200000 in
example (m : ℕ)  :
    (1 ≤ m) ↔ (1 < m) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((1 ≤ m) ↔ (1 < m))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((1 ≤ m) ↔ (1 < m))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((1 ≤ m) ↔ (1 < m))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((1 ≤ m) ↔ (1 < m))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((1 ≤ m) ↔ (1 < m))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((1 ≤ m) ↔ (1 < m))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 ≤ m) ↔ (1 < m)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 ≤ m) ↔ (1 < m)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 ≤ m) ↔ (1 < m)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 ≤ m) ↔ (1 < m)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 ≤ m) ↔ (1 < m)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 ≤ m) ↔ (1 < m)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ) (hm : m ≥ 1), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (m ≥ 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (m ≥ 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (m ≥ 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (m ≥ 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (m ≥ 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (m ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (m ≥ 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (m ≥ 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) ↔
    (∀ (m : ℕ) (hm : m ≥ 1), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) ↔
    (∀ (m : ℕ) (hm : m ≥ 1), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) ↔
    (∀ (m : ℕ) (hm : m ≥ 1), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) ↔
    (∀ (m : ℕ) (hm : m ≥ 1), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ) (hm₀ : 1 ≤ m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) ↔
    (∀ (m : ℕ) (hm₀ : 1 ≤ m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) ↔
    (∀ (m : ℕ) (hm₀ : 1 ≤ m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) ↔
    (∀ (m : ℕ) (hm₀ : 1 ≤ m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) ↔
    (∀ (m : ℕ) (hm₀ : 1 ≤ m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ) (hm : ¬(m < 1)), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (¬(m < 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (¬(m < 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (¬(m < 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (¬(m < 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (¬(m < 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (¬(m < 1)) := by
  omega

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (¬(m < 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (¬(m < 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) ↔
    (∀ (m : ℕ) (hm : ¬(m < 1)), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) ↔
    (∀ (m : ℕ) (hm : ¬(m < 1)), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) ↔
    (∀ (m : ℕ) (hm : ¬(m < 1)), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) ↔
    (∀ (m : ℕ) (hm : ¬(m < 1)), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ) (hm : 0 < m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (0 < m) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (0 < m) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (0 < m) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (0 < m) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (0 < m) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (0 < m) := by
  omega

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (0 < m) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (0 < m) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) ↔
    (∀ (m : ℕ) (hm : 0 < m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) ↔
    (∀ (m : ℕ) (hm : 0 < m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) ↔
    (∀ (m : ℕ) (hm : 0 < m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) ↔
    (∀ (m : ℕ) (hm : 0 < m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ) (hm : m > 1), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) →
    (∀ (m : ℕ) (hm : m > 1), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) →
    (∀ (m : ℕ) (hm : m > 1), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) →
    (∀ (m : ℕ) (hm : m > 1), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) →
    (∀ (m : ℕ) (hm : m > 1), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) →
    (∀ (m : ℕ) (hm : m > 1), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) →
    (∀ (m : ℕ) (hm : m > 1), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) →
    (∀ (m : ℕ) (hm : m > 1), ∑ i ∈ Finset.range m, f i + (if Even m then 1 else 0) = f (m + 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (m : ℕ)  :
    (1 ≤ m) ↔ (m > 1) := by
  omega

set_option maxHeartbeats 200000 in
example (m : ℕ)  :
    (1 ≤ m) ↔ (m > 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (m : ℕ)  :
    (1 ≤ m) ↔ (m > 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (m : ℕ)  :
    (1 ≤ m) ↔ (m > 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (m : ℕ)  :
    (1 ≤ m) ↔ (m > 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (m : ℕ)  :
    (1 ≤ m) ↔ (m > 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example (m : ℕ)  :
    (1 ≤ m) ↔ (m > 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((1 ≤ m) ↔ (m > 1))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((1 ≤ m) ↔ (m > 1))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((1 ≤ m) ↔ (m > 1))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((1 ≤ m) ↔ (m > 1))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((1 ≤ m) ↔ (m > 1))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((1 ≤ m) ↔ (m > 1))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 ≤ m) ↔ (m > 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 ≤ m) ↔ (m > 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 ≤ m) ↔ (m > 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 ≤ m) ↔ (m > 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 ≤ m) ↔ (m > 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 ≤ m) ↔ (m > 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (m : ℕ) (hm : 1 ≤ m) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (m : ℕ) (hm : 1 ≤ m) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (m : ℕ) (hm : 1 ≤ m) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (m : ℕ) (hm : 1 ≤ m) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (m : ℕ) (hm : 1 ≤ m) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
