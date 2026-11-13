import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# A nonlinear recurrence sequence

For even $n$, $a(n+2)$ is the greatest integer such that $a(n+2)/a(n+1) < a(n+1)/a(n)$;
for odd $n$, the least integer such that $a(n+2)/a(n+1) > a(n+1)/a(n)$;
$a(0) = 4, a(1) = 16$.

*References:*
- [A022030](https://oeis.org/A022030)
-/

section

namespace OeisA22030

/--
For even $n$, $a(n+2)$ is the greatest integer such that $a(n+2)/a(n+1) < a(n+1)/a(n)$;
for odd $n$, the least integer such that $a(n+2)/a(n+1) > a(n+1)/a(n)$;
$a(0) = 4, a(1) = 16$.
-/
def a (n : ℕ) : ℕ :=
  match n with
  | 0 => 4
  | 1 => 16
  | n + 2 =>
    if Even n then
      (a (n + 1) ^ 2 + a n - 1) / a n - 1
    else
      (a (n + 1) ^ 2) / a n + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 5 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) →
    (∀ (n : ℕ) (hn : 5 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) →
    (∀ (n : ℕ) (hn : 5 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) →
    (∀ (n : ℕ) (hn : 5 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) →
    (∀ (n : ℕ) (hn : 5 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) →
    (∀ (n : ℕ) (hn : 5 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) →
    (∀ (n : ℕ) (hn : 5 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) →
    (∀ (n : ℕ) (hn : 5 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (4 ≤ n) ↔ (5 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (4 ≤ n) ↔ (5 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (4 ≤ n) ↔ (5 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (4 ≤ n) ↔ (5 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (4 ≤ n) ↔ (5 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (4 ≤ n) ↔ (5 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (4 ≤ n) ↔ (5 ≤ n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((4 ≤ n) ↔ (5 ≤ n))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((4 ≤ n) ↔ (5 ≤ n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((4 ≤ n) ↔ (5 ≤ n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((4 ≤ n) ↔ (5 ≤ n))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((4 ≤ n) ↔ (5 ≤ n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((4 ≤ n) ↔ (5 ≤ n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((4 ≤ n) ↔ (5 ≤ n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((4 ≤ n) ↔ (5 ≤ n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (5 ≤ n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (5 ≤ n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (5 ≤ n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (5 ≤ n)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (5 ≤ n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (5 ≤ n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (5 ≤ n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (5 ≤ n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 4), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (4 ≤ n) ↔ (n ≥ 4) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (4 ≤ n) ↔ (n ≥ 4) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (4 ≤ n) ↔ (n ≥ 4) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (4 ≤ n) ↔ (n ≥ 4) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (4 ≤ n) ↔ (n ≥ 4) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (4 ≤ n) ↔ (n ≥ 4) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (4 ≤ n) ↔ (n ≥ 4) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (4 ≤ n) ↔ (n ≥ 4) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) ↔
    (∀ (n : ℕ) (hn : n ≥ 4), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) ↔
    (∀ (n : ℕ) (hn : n ≥ 4), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) ↔
    (∀ (n : ℕ) (hn : n ≥ 4), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) ↔
    (∀ (n : ℕ) (hn : n ≥ 4), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn₀ : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) ↔
    (∀ (n : ℕ) (hn₀ : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) ↔
    (∀ (n : ℕ) (hn₀ : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) ↔
    (∀ (n : ℕ) (hn₀ : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) ↔
    (∀ (n : ℕ) (hn₀ : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : ¬(n < 4)), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (4 ≤ n) ↔ (¬(n < 4)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (4 ≤ n) ↔ (¬(n < 4)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (4 ≤ n) ↔ (¬(n < 4)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (4 ≤ n) ↔ (¬(n < 4)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (4 ≤ n) ↔ (¬(n < 4)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (4 ≤ n) ↔ (¬(n < 4)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (4 ≤ n) ↔ (¬(n < 4)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (4 ≤ n) ↔ (¬(n < 4)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) ↔
    (∀ (n : ℕ) (hn : ¬(n < 4)), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) ↔
    (∀ (n : ℕ) (hn : ¬(n < 4)), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) ↔
    (∀ (n : ℕ) (hn : ¬(n < 4)), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) ↔
    (∀ (n : ℕ) (hn : ¬(n < 4)), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 < n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (4 ≤ n) ↔ (3 < n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (4 ≤ n) ↔ (3 < n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (4 ≤ n) ↔ (3 < n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (4 ≤ n) ↔ (3 < n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (4 ≤ n) ↔ (3 < n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (4 ≤ n) ↔ (3 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (4 ≤ n) ↔ (3 < n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (4 ≤ n) ↔ (3 < n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) ↔
    (∀ (n : ℕ) (hn : 3 < n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) ↔
    (∀ (n : ℕ) (hn : 3 < n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) ↔
    (∀ (n : ℕ) (hn : 3 < n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) ↔
    (∀ (n : ℕ) (hn : 3 < n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 5), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) →
    (∀ (n : ℕ) (hn : n ≥ 5), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) →
    (∀ (n : ℕ) (hn : n ≥ 5), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) →
    (∀ (n : ℕ) (hn : n ≥ 5), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) →
    (∀ (n : ℕ) (hn : n ≥ 5), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) →
    (∀ (n : ℕ) (hn : n ≥ 5), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) →
    (∀ (n : ℕ) (hn : n ≥ 5), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) →
    (∀ (n : ℕ) (hn : n ≥ 5), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (4 ≤ n) ↔ (n ≥ 5) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (4 ≤ n) ↔ (n ≥ 5) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (4 ≤ n) ↔ (n ≥ 5) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (4 ≤ n) ↔ (n ≥ 5) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (4 ≤ n) ↔ (n ≥ 5) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (4 ≤ n) ↔ (n ≥ 5) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (4 ≤ n) ↔ (n ≥ 5) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((4 ≤ n) ↔ (n ≥ 5))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((4 ≤ n) ↔ (n ≥ 5))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((4 ≤ n) ↔ (n ≥ 5))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((4 ≤ n) ↔ (n ≥ 5))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((4 ≤ n) ↔ (n ≥ 5))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((4 ≤ n) ↔ (n ≥ 5))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((4 ≤ n) ↔ (n ≥ 5))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((4 ≤ n) ↔ (n ≥ 5))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (n ≥ 5)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (n ≥ 5)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (n ≥ 5)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (n ≥ 5)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (n ≥ 5)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (n ≥ 5)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (n ≥ 5)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (n ≥ 5)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 4 < n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) →
    (∀ (n : ℕ) (hn : 4 < n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) →
    (∀ (n : ℕ) (hn : 4 < n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) →
    (∀ (n : ℕ) (hn : 4 < n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) →
    (∀ (n : ℕ) (hn : 4 < n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) →
    (∀ (n : ℕ) (hn : 4 < n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) →
    (∀ (n : ℕ) (hn : 4 < n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) →
    (∀ (n : ℕ) (hn : 4 < n), a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (4 ≤ n) ↔ (4 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (4 ≤ n) ↔ (4 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (4 ≤ n) ↔ (4 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (4 ≤ n) ↔ (4 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (4 ≤ n) ↔ (4 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (4 ≤ n) ↔ (4 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (4 ≤ n) ↔ (4 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((4 ≤ n) ↔ (4 < n))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((4 ≤ n) ↔ (4 < n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((4 ≤ n) ↔ (4 < n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((4 ≤ n) ↔ (4 < n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((4 ≤ n) ↔ (4 < n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((4 ≤ n) ↔ (4 < n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((4 ≤ n) ↔ (4 < n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (4 < n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (4 < n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (4 < n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (4 < n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (4 < n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (4 < n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (4 < n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 4 ≤ n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 4 ≤ n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 4 ≤ n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 4 ≤ n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 4 ≤ n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
