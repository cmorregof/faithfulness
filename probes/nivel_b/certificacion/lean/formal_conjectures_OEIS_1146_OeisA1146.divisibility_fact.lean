import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# $a(n) = 2^(2^n)$

*References:*
- [A001146](https://oeis.org/A001146)
-/

section

namespace OeisA1146

/--
The primary defining sequence `a`.
$a(n) = 2^{2^n}$.
-/
def a (n : ℕ) : ℕ := 2 ^ (2 ^ n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 < n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : 2 < n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : 2 < n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : 2 < n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : 2 < n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : 2 < n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : 2 < n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : 2 < n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (2 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (2 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (2 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (2 < n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (2 < n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (2 < n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (2 < n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (2 < n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (2 < n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (3 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (3 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (3 ≤ n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (3 ≤ n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (3 ≤ n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (3 ≤ n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (3 ≤ n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (3 ≤ n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (3 ≤ n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (3 ≤ n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 2), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (n ≥ 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (n ≥ 2) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (n ≥ 2) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (n ≥ 2) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (n ≥ 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (n ≥ 2) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (n ≥ 2) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (n ≥ 2) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) ↔
    (∀ (n : ℕ) (hn : n ≥ 2), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) ↔
    (∀ (n : ℕ) (hn : n ≥ 2), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) ↔
    (∀ (n : ℕ) (hn : n ≥ 2), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) ↔
    (∀ (n : ℕ) (hn : n ≥ 2), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn₀ : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) ↔
    (∀ (n : ℕ) (hn₀ : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) ↔
    (∀ (n : ℕ) (hn₀ : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) ↔
    (∀ (n : ℕ) (hn₀ : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) ↔
    (∀ (n : ℕ) (hn₀ : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : ¬(n < 2)), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) ↔
    (∀ (n : ℕ) (hn : ¬(n < 2)), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) ↔
    (∀ (n : ℕ) (hn : ¬(n < 2)), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) ↔
    (∀ (n : ℕ) (hn : ¬(n < 2)), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) ↔
    (∀ (n : ℕ) (hn : ¬(n < 2)), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (1 < n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (1 < n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (1 < n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (1 < n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (1 < n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (1 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (1 < n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (1 < n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) ↔
    (∀ (n : ℕ) (hn : 1 < n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) ↔
    (∀ (n : ℕ) (hn : 1 < n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) ↔
    (∀ (n : ℕ) (hn : 1 < n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) ↔
    (∀ (n : ℕ) (hn : 1 < n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 2), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : n > 2), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : n > 2), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : n > 2), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : n > 2), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : n > 2), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : n > 2), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : n > 2), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n > 2) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n > 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n > 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n > 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n > 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n > 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n > 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n > 2))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n > 2))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n > 2))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n > 2))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n > 2))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n > 2))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n > 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n > 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n > 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n > 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n > 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n > 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 3), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : n ≥ 3), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : n ≥ 3), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : n ≥ 3), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : n ≥ 3), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : n ≥ 3), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : n ≥ 3), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : n ≥ 3), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n ≥ 3) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n ≥ 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n ≥ 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n ≥ 3))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n ≥ 3))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n ≥ 3))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n ≥ 3))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n ≥ 3))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n ≥ 3))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n ≥ 3))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n ≥ 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n ≥ 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n ≥ 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n ≥ 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n ≥ 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n ≥ 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n ≥ 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (1 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (1 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (1 ≤ n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (1 ≤ n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (1 ≤ n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (1 ≤ n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (1 ≤ n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (1 ≤ n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (1 ≤ n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (1 ≤ n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (1 ≤ n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (1 ≤ n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (1 ≤ n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (1 ≤ n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (1 ≤ n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n), (((a n)^4 - 1) : ℕ) ∣ (3^(a n) - 1 : ℕ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), (((a n)^4 - 1) : ℕ) ∣ (3^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), (((a n)^4 - 1) : ℕ) ∣ (3^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), (((a n)^4 - 1) : ℕ) ∣ (3^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), (((a n)^4 - 1) : ℕ) ∣ (3^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), (((a n)^4 - 1) : ℕ) ∣ (3^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), (((a n)^4 - 1) : ℕ) ∣ (3^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), (((a n)^4 - 1) : ℕ) ∣ (3^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : 1 < n), (((a n)^4 - 1) : ℕ) ∣ (3^(a n) - 1 : ℕ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : 1 < n), (((a n)^4 - 1) : ℕ) ∣ (3^(a n) - 1 : ℕ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : 1 < n), (((a n)^4 - 1) : ℕ) ∣ (3^(a n) - 1 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : 1 < n), (((a n)^4 - 1) : ℕ) ∣ (3^(a n) - 1 : ℕ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : 1 < n), (((a n)^4 - 1) : ℕ) ∣ (3^(a n) - 1 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : 1 < n), (((a n)^4 - 1) : ℕ) ∣ (3^(a n) - 1 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) →
    (∀ (n : ℕ) (hn : 1 < n), (((a n)^4 - 1) : ℕ) ∣ (3^(a n) - 1 : ℕ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (2 ≤ n) ∧ (¬((((a n)^4 - 1) : ℕ) ∣ (3^(a n) - 1 : ℕ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (2 ≤ n) ∧ (¬((((a n)^4 - 1) : ℕ) ∣ (3^(a n) - 1 : ℕ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (2 ≤ n) ∧ (¬((((a n)^4 - 1) : ℕ) ∣ (3^(a n) - 1 : ℕ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (2 ≤ n) ∧ (¬((((a n)^4 - 1) : ℕ) ∣ (3^(a n) - 1 : ℕ))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (2 ≤ n) ∧ (¬((((a n)^4 - 1) : ℕ) ∣ (3^(a n) - 1 : ℕ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (2 ≤ n) ∧ (¬((((a n)^4 - 1) : ℕ) ∣ (3^(a n) - 1 : ℕ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (2 ≤ n) ∧ (¬((((a n)^4 - 1) : ℕ) ∣ (3^(a n) - 1 : ℕ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) ↔ ((((a n)^4 - 1) : ℕ) ∣ (3^(a n) - 1 : ℕ))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) ↔ ((((a n)^4 - 1) : ℕ) ∣ (3^(a n) - 1 : ℕ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) ↔ ((((a n)^4 - 1) : ℕ) ∣ (3^(a n) - 1 : ℕ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) ↔ ((((a n)^4 - 1) : ℕ) ∣ (3^(a n) - 1 : ℕ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) ↔ ((((a n)^4 - 1) : ℕ) ∣ (3^(a n) - 1 : ℕ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) ↔ ((((a n)^4 - 1) : ℕ) ∣ (3^(a n) - 1 : ℕ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ)) ↔ ((((a n)^4 - 1) : ℕ) ∣ (3^(a n) - 1 : ℕ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 2 ≤ n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 2 ≤ n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 2 ≤ n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 2 ≤ n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 2 ≤ n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
