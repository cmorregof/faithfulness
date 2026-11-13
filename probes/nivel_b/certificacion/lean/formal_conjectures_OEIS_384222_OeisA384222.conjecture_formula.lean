import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Lengths of the 2-dense sublists of divisors of $n$

Write the divisors of $n$ in increasing order and split this list between consecutive divisors
$d < d'$ with $d' > 2d$. The pieces are the 2-dense sublists of divisors of $n$. Row $n$ of the
triangle lists their lengths. Row $n$ of A384225 lists the numbers of odd terms in them.

*References:*
- [A384222](https://oeis.org/A384222)
- [A384225](https://oeis.org/A384225)
-/

section

namespace OeisA384222

/-- The divisors of $n$ in increasing order. -/
def divisorList (n : ℕ) : List ℕ := (List.range' 1 n).filter (· ∣ n)

/-- The 2-dense sublists of divisors of $n$. -/
def denseSublists (n : ℕ) : List (List ℕ) :=
  (divisorList n).splitBy fun d d' => d' ≤ 2 * d

/-- Row $n$ of the triangle: the lengths of the 2-dense sublists of divisors of $n$. -/
def row (n : ℕ) : List ℕ := (denseSublists n).map List.length

/-- Row $n$ of A384225: the numbers of odd terms in the 2-dense sublists of divisors of $n$. -/
def oddRow (n : ℕ) : List ℕ := (denseSublists n).map (List.countP fun d => d % 2 = 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 3 n + 1) * ·)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 3 n + 1) * ·)) →
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 3 n + 1) * ·)) →
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 3 n + 1) * ·)) →
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 3 n + 1) * ·)) →
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 3 n + 1) * ·)) →
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 3 n + 1) * ·)) →
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 3 n + 1) * ·)) →
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) →
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 3 n + 1) * ·)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) →
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 3 n + 1) * ·)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) →
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 3 n + 1) * ·)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) →
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 3 n + 1) * ·)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) →
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 3 n + 1) * ·)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) →
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 3 n + 1) * ·)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) →
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 3 n + 1) * ·)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(row n = (oddRow n).map ((padicValNat 3 n + 1) * ·))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(row n = (oddRow n).map ((padicValNat 3 n + 1) * ·))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(row n = (oddRow n).map ((padicValNat 3 n + 1) * ·))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(row n = (oddRow n).map ((padicValNat 3 n + 1) * ·))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(row n = (oddRow n).map ((padicValNat 3 n + 1) * ·))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(row n = (oddRow n).map ((padicValNat 3 n + 1) * ·))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(row n = (oddRow n).map ((padicValNat 3 n + 1) * ·))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) ↔ (row n = (oddRow n).map ((padicValNat 3 n + 1) * ·))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) ↔ (row n = (oddRow n).map ((padicValNat 3 n + 1) * ·))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) ↔ (row n = (oddRow n).map ((padicValNat 3 n + 1) * ·))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) ↔ (row n = (oddRow n).map ((padicValNat 3 n + 1) * ·))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) ↔ (row n = (oddRow n).map ((padicValNat 3 n + 1) * ·))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) ↔ (row n = (oddRow n).map ((padicValNat 3 n + 1) * ·))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) ↔ (row n = (oddRow n).map ((padicValNat 3 n + 1) * ·))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 0), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (n > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (n > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (n > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (n > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (n > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (n > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (n > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (n > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) ↔
    (∀ (n : ℕ) (hn : n > 0), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) ↔
    (∀ (n : ℕ) (hn : n > 0), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) ↔
    (∀ (n : ℕ) (hn : n > 0), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) ↔
    (∀ (n : ℕ) (hn : n > 0), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn₀ : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) ↔
    (∀ (n : ℕ) (hn₀ : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) ↔
    (∀ (n : ℕ) (hn₀ : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) ↔
    (∀ (n : ℕ) (hn₀ : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) ↔
    (∀ (n : ℕ) (hn₀ : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : ¬(n ≤ 0)), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 0)), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 0)), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 0)), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 0)), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 0), row n = (oddRow n).map ((padicValNat 3 n + 1) * ·)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), row n = (oddRow n).map ((padicValNat 3 n + 1) * ·)) →
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), row n = (oddRow n).map ((padicValNat 3 n + 1) * ·)) →
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), row n = (oddRow n).map ((padicValNat 3 n + 1) * ·)) →
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), row n = (oddRow n).map ((padicValNat 3 n + 1) * ·)) →
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), row n = (oddRow n).map ((padicValNat 3 n + 1) * ·)) →
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), row n = (oddRow n).map ((padicValNat 3 n + 1) * ·)) →
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), row n = (oddRow n).map ((padicValNat 3 n + 1) * ·)) →
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) →
    (∀ (n : ℕ) (hn : n > 0), row n = (oddRow n).map ((padicValNat 3 n + 1) * ·)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) →
    (∀ (n : ℕ) (hn : n > 0), row n = (oddRow n).map ((padicValNat 3 n + 1) * ·)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) →
    (∀ (n : ℕ) (hn : n > 0), row n = (oddRow n).map ((padicValNat 3 n + 1) * ·)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) →
    (∀ (n : ℕ) (hn : n > 0), row n = (oddRow n).map ((padicValNat 3 n + 1) * ·)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) →
    (∀ (n : ℕ) (hn : n > 0), row n = (oddRow n).map ((padicValNat 3 n + 1) * ·)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) →
    (∀ (n : ℕ) (hn : n > 0), row n = (oddRow n).map ((padicValNat 3 n + 1) * ·)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) →
    (∀ (n : ℕ) (hn : n > 0), row n = (oddRow n).map ((padicValNat 3 n + 1) * ·)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(row n = (oddRow n).map ((padicValNat 3 n + 1) * ·))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(row n = (oddRow n).map ((padicValNat 3 n + 1) * ·))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(row n = (oddRow n).map ((padicValNat 3 n + 1) * ·))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(row n = (oddRow n).map ((padicValNat 3 n + 1) * ·))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(row n = (oddRow n).map ((padicValNat 3 n + 1) * ·))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(row n = (oddRow n).map ((padicValNat 3 n + 1) * ·))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(row n = (oddRow n).map ((padicValNat 3 n + 1) * ·))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) ↔ (row n = (oddRow n).map ((padicValNat 3 n + 1) * ·))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) ↔ (row n = (oddRow n).map ((padicValNat 3 n + 1) * ·))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) ↔ (row n = (oddRow n).map ((padicValNat 3 n + 1) * ·))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) ↔ (row n = (oddRow n).map ((padicValNat 3 n + 1) * ·))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) ↔ (row n = (oddRow n).map ((padicValNat 3 n + 1) * ·))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) ↔ (row n = (oddRow n).map ((padicValNat 3 n + 1) * ·))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) ↔ (row n = (oddRow n).map ((padicValNat 3 n + 1) * ·))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), row n = (oddRow n).map ((padicValNat 3 n + 1) * ·)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), row n = (oddRow n).map ((padicValNat 3 n + 1) * ·)) →
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), row n = (oddRow n).map ((padicValNat 3 n + 1) * ·)) →
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), row n = (oddRow n).map ((padicValNat 3 n + 1) * ·)) →
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), row n = (oddRow n).map ((padicValNat 3 n + 1) * ·)) →
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), row n = (oddRow n).map ((padicValNat 3 n + 1) * ·)) →
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), row n = (oddRow n).map ((padicValNat 3 n + 1) * ·)) →
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), row n = (oddRow n).map ((padicValNat 3 n + 1) * ·)) →
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), row n = (oddRow n).map ((padicValNat 3 n + 1) * ·)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), row n = (oddRow n).map ((padicValNat 3 n + 1) * ·)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), row n = (oddRow n).map ((padicValNat 3 n + 1) * ·)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), row n = (oddRow n).map ((padicValNat 3 n + 1) * ·)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), row n = (oddRow n).map ((padicValNat 3 n + 1) * ·)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), row n = (oddRow n).map ((padicValNat 3 n + 1) * ·)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), row n = (oddRow n).map ((padicValNat 3 n + 1) * ·)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(row n = (oddRow n).map ((padicValNat 3 n + 1) * ·))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(row n = (oddRow n).map ((padicValNat 3 n + 1) * ·))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(row n = (oddRow n).map ((padicValNat 3 n + 1) * ·))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(row n = (oddRow n).map ((padicValNat 3 n + 1) * ·))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(row n = (oddRow n).map ((padicValNat 3 n + 1) * ·))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(row n = (oddRow n).map ((padicValNat 3 n + 1) * ·))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(row n = (oddRow n).map ((padicValNat 3 n + 1) * ·))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) ↔ (row n = (oddRow n).map ((padicValNat 3 n + 1) * ·))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) ↔ (row n = (oddRow n).map ((padicValNat 3 n + 1) * ·))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) ↔ (row n = (oddRow n).map ((padicValNat 3 n + 1) * ·))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) ↔ (row n = (oddRow n).map ((padicValNat 3 n + 1) * ·))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) ↔ (row n = (oddRow n).map ((padicValNat 3 n + 1) * ·))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) ↔ (row n = (oddRow n).map ((padicValNat 3 n + 1) * ·))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((row n = (oddRow n).map ((padicValNat 2 n + 1) * ·)) ↔ (row n = (oddRow n).map ((padicValNat 3 n + 1) * ·))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 0 < n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 0 < n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 0 < n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 0 < n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 0 < n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
