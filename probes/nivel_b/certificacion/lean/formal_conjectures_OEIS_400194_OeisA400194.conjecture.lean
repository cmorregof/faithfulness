import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Maximum number of terms in a 2-dense sublist of divisors of $n$

Write the divisors of $n$ in increasing order and split this list between consecutive divisors
$d < d'$ with $d' > 2d$. The pieces are the 2-dense sublists of divisors of $n$. The sequence
gives the maximum number of terms in such a sublist.

*References:*
- [A400194](https://oeis.org/A400194)
- [A400195](https://oeis.org/A400195)
- [A384222](https://oeis.org/A384222)
-/

section

namespace OeisA400194

/-- The divisors of $n$ in increasing order. -/
def divisorList (n : ℕ) : List ℕ := (List.range' 1 n).filter (· ∣ n)

/-- The 2-dense sublists of divisors of $n$. -/
def denseSublists (n : ℕ) : List (List ℕ) :=
  (divisorList n).splitBy fun d d' => d' ≤ 2 * d

/-- The maximum number of terms in a 2-dense sublist of divisors of $n$. -/
def a (n : ℕ) : ℕ := ((denseSublists n).map List.length).foldr max 0

/-- The maximum number of odd terms in a 2-dense sublist of divisors of $n$ (A400195). -/
def b (n : ℕ) : ℕ := ((denseSublists n).map (List.countP fun d => d % 2 = 1)).foldr max 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 3 n + 1) * b n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 3 n + 1) * b n) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 3 n + 1) * b n) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 3 n + 1) * b n) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 3 n + 1) * b n) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 3 n + 1) * b n) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 3 n + 1) * b n) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 3 n + 1) * b n) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 3 n + 1) * b n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 3 n + 1) * b n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 3 n + 1) * b n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 3 n + 1) * b n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 3 n + 1) * b n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 3 n + 1) * b n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 3 n + 1) * b n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(a n = (padicValNat 3 n + 1) * b n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(a n = (padicValNat 3 n + 1) * b n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(a n = (padicValNat 3 n + 1) * b n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(a n = (padicValNat 3 n + 1) * b n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(a n = (padicValNat 3 n + 1) * b n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(a n = (padicValNat 3 n + 1) * b n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(a n = (padicValNat 3 n + 1) * b n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = (padicValNat 2 n + 1) * b n) ↔ (a n = (padicValNat 3 n + 1) * b n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = (padicValNat 2 n + 1) * b n) ↔ (a n = (padicValNat 3 n + 1) * b n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = (padicValNat 2 n + 1) * b n) ↔ (a n = (padicValNat 3 n + 1) * b n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = (padicValNat 2 n + 1) * b n) ↔ (a n = (padicValNat 3 n + 1) * b n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = (padicValNat 2 n + 1) * b n) ↔ (a n = (padicValNat 3 n + 1) * b n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = (padicValNat 2 n + 1) * b n) ↔ (a n = (padicValNat 3 n + 1) * b n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = (padicValNat 2 n + 1) * b n) ↔ (a n = (padicValNat 3 n + 1) * b n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 0), a n = (padicValNat 2 n + 1) * b n

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
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) ↔
    (∀ (n : ℕ) (hn : n > 0), a n = (padicValNat 2 n + 1) * b n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) ↔
    (∀ (n : ℕ) (hn : n > 0), a n = (padicValNat 2 n + 1) * b n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) ↔
    (∀ (n : ℕ) (hn : n > 0), a n = (padicValNat 2 n + 1) * b n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) ↔
    (∀ (n : ℕ) (hn : n > 0), a n = (padicValNat 2 n + 1) * b n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn₀ : 0 < n), a n = (padicValNat 2 n + 1) * b n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) ↔
    (∀ (n : ℕ) (hn₀ : 0 < n), a n = (padicValNat 2 n + 1) * b n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) ↔
    (∀ (n : ℕ) (hn₀ : 0 < n), a n = (padicValNat 2 n + 1) * b n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) ↔
    (∀ (n : ℕ) (hn₀ : 0 < n), a n = (padicValNat 2 n + 1) * b n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) ↔
    (∀ (n : ℕ) (hn₀ : 0 < n), a n = (padicValNat 2 n + 1) * b n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : ¬(n ≤ 0)), a n = (padicValNat 2 n + 1) * b n

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
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 0)), a n = (padicValNat 2 n + 1) * b n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 0)), a n = (padicValNat 2 n + 1) * b n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 0)), a n = (padicValNat 2 n + 1) * b n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 0)), a n = (padicValNat 2 n + 1) * b n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), a n = (padicValNat 2 n + 1) * b n

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
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n), a n = (padicValNat 2 n + 1) * b n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n), a n = (padicValNat 2 n + 1) * b n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n), a n = (padicValNat 2 n + 1) * b n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n), a n = (padicValNat 2 n + 1) * b n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 0), a n = (padicValNat 3 n + 1) * b n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), a n = (padicValNat 3 n + 1) * b n) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), a n = (padicValNat 3 n + 1) * b n) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), a n = (padicValNat 3 n + 1) * b n) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), a n = (padicValNat 3 n + 1) * b n) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), a n = (padicValNat 3 n + 1) * b n) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), a n = (padicValNat 3 n + 1) * b n) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), a n = (padicValNat 3 n + 1) * b n) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) →
    (∀ (n : ℕ) (hn : n > 0), a n = (padicValNat 3 n + 1) * b n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) →
    (∀ (n : ℕ) (hn : n > 0), a n = (padicValNat 3 n + 1) * b n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) →
    (∀ (n : ℕ) (hn : n > 0), a n = (padicValNat 3 n + 1) * b n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) →
    (∀ (n : ℕ) (hn : n > 0), a n = (padicValNat 3 n + 1) * b n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) →
    (∀ (n : ℕ) (hn : n > 0), a n = (padicValNat 3 n + 1) * b n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) →
    (∀ (n : ℕ) (hn : n > 0), a n = (padicValNat 3 n + 1) * b n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) →
    (∀ (n : ℕ) (hn : n > 0), a n = (padicValNat 3 n + 1) * b n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(a n = (padicValNat 3 n + 1) * b n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(a n = (padicValNat 3 n + 1) * b n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(a n = (padicValNat 3 n + 1) * b n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(a n = (padicValNat 3 n + 1) * b n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(a n = (padicValNat 3 n + 1) * b n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(a n = (padicValNat 3 n + 1) * b n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(a n = (padicValNat 3 n + 1) * b n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = (padicValNat 2 n + 1) * b n) ↔ (a n = (padicValNat 3 n + 1) * b n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = (padicValNat 2 n + 1) * b n) ↔ (a n = (padicValNat 3 n + 1) * b n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = (padicValNat 2 n + 1) * b n) ↔ (a n = (padicValNat 3 n + 1) * b n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = (padicValNat 2 n + 1) * b n) ↔ (a n = (padicValNat 3 n + 1) * b n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = (padicValNat 2 n + 1) * b n) ↔ (a n = (padicValNat 3 n + 1) * b n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = (padicValNat 2 n + 1) * b n) ↔ (a n = (padicValNat 3 n + 1) * b n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = (padicValNat 2 n + 1) * b n) ↔ (a n = (padicValNat 3 n + 1) * b n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n), a n = (padicValNat 2 n + 1) * b n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) →
    (∀ (n : ℕ) (hn : 1 < n), a n = (padicValNat 2 n + 1) * b n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) →
    (∀ (n : ℕ) (hn : 1 < n), a n = (padicValNat 2 n + 1) * b n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) →
    (∀ (n : ℕ) (hn : 1 < n), a n = (padicValNat 2 n + 1) * b n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) →
    (∀ (n : ℕ) (hn : 1 < n), a n = (padicValNat 2 n + 1) * b n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) →
    (∀ (n : ℕ) (hn : 1 < n), a n = (padicValNat 2 n + 1) * b n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) →
    (∀ (n : ℕ) (hn : 1 < n), a n = (padicValNat 2 n + 1) * b n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) →
    (∀ (n : ℕ) (hn : 1 < n), a n = (padicValNat 2 n + 1) * b n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (0 < n) ↔ (1 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (0 < n) ↔ (1 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
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
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), a n = (padicValNat 3 n + 1) * b n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n = (padicValNat 3 n + 1) * b n) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n = (padicValNat 3 n + 1) * b n) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n = (padicValNat 3 n + 1) * b n) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n = (padicValNat 3 n + 1) * b n) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n = (padicValNat 3 n + 1) * b n) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n = (padicValNat 3 n + 1) * b n) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n = (padicValNat 3 n + 1) * b n) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n = (padicValNat 3 n + 1) * b n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n = (padicValNat 3 n + 1) * b n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n = (padicValNat 3 n + 1) * b n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n = (padicValNat 3 n + 1) * b n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n = (padicValNat 3 n + 1) * b n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n = (padicValNat 3 n + 1) * b n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (padicValNat 2 n + 1) * b n) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n = (padicValNat 3 n + 1) * b n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(a n = (padicValNat 3 n + 1) * b n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(a n = (padicValNat 3 n + 1) * b n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(a n = (padicValNat 3 n + 1) * b n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(a n = (padicValNat 3 n + 1) * b n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(a n = (padicValNat 3 n + 1) * b n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(a n = (padicValNat 3 n + 1) * b n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(a n = (padicValNat 3 n + 1) * b n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = (padicValNat 2 n + 1) * b n) ↔ (a n = (padicValNat 3 n + 1) * b n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = (padicValNat 2 n + 1) * b n) ↔ (a n = (padicValNat 3 n + 1) * b n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = (padicValNat 2 n + 1) * b n) ↔ (a n = (padicValNat 3 n + 1) * b n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = (padicValNat 2 n + 1) * b n) ↔ (a n = (padicValNat 3 n + 1) * b n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = (padicValNat 2 n + 1) * b n) ↔ (a n = (padicValNat 3 n + 1) * b n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = (padicValNat 2 n + 1) * b n) ↔ (a n = (padicValNat 3 n + 1) * b n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = (padicValNat 2 n + 1) * b n) ↔ (a n = (padicValNat 3 n + 1) * b n)) :=
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
