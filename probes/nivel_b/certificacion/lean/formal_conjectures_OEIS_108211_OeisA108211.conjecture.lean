import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# $a(n) = 16n^2 + 1$

*References:*
- [A108211](https://oeis.org/A108211)
-/

section

namespace OeisA108211

/--
The primary defining sequence `a`.
`a n` is defined as $16n^2 + 1$.
-/
def a (n : ℕ) : ℕ := 16 * n ^ 2 + 1

open Real

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n > 0) ∧ (¬((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n > 0) ∧ (¬((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n > 0) ∧ (¬((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n > 0) ∧ (¬((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n > 0) ∧ (¬((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n > 0) ∧ (¬((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n > 0) ∧ (¬((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n > 0) ∧ (¬((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) ↔ ((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) ↔ ((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) ↔ ((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) ↔ ((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) ↔ ((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) ↔ ((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) ↔ ((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) ↔ ((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 0) ↔ (0 < n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 0) ↔ (0 < n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 0) ↔ (0 < n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 0) ↔ (0 < n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 0) ↔ (0 < n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 0) ↔ (0 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 0) ↔ (0 < n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 0) ↔ (0 < n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) ↔
    (∀ (n : ℕ) (hn : 0 < n), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) ↔
    (∀ (n : ℕ) (hn : 0 < n), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) ↔
    (∀ (n : ℕ) (hn : 0 < n), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) ↔
    (∀ (n : ℕ) (hn : 0 < n), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn₀ : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) ↔
    (∀ (n : ℕ) (hn₀ : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) ↔
    (∀ (n : ℕ) (hn₀ : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) ↔
    (∀ (n : ℕ) (hn₀ : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) ↔
    (∀ (n : ℕ) (hn₀ : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : ¬(n ≤ 0)), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 0) ↔ (¬(n ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 0) ↔ (¬(n ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 0) ↔ (¬(n ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 0) ↔ (¬(n ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 0) ↔ (¬(n ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 0) ↔ (¬(n ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 0) ↔ (¬(n ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 0) ↔ (¬(n ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 0)), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 0)), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 0)), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 0)), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 1), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 0) ↔ (n ≥ 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 0) ↔ (n ≥ 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 0) ↔ (n ≥ 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 0) ↔ (n ≥ 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 0) ↔ (n ≥ 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 0) ↔ (n ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 0) ↔ (n ≥ 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 0) ↔ (n ≥ 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) ↔
    (∀ (n : ℕ) (hn : n ≥ 1), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) ↔
    (∀ (n : ℕ) (hn : n ≥ 1), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) ↔
    (∀ (n : ℕ) (hn : n ≥ 1), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) ↔
    (∀ (n : ℕ) (hn : n ≥ 1), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), (a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), (a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), (a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), (a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), (a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), (a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), (a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), (a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), (a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), (a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), (a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), (a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), (a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), (a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), (a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n > 0) ∧ (¬((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n > 0) ∧ (¬((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n > 0) ∧ (¬((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n > 0) ∧ (¬((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n > 0) ∧ (¬((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n > 0) ∧ (¬((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n > 0) ∧ (¬((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n > 0) ∧ (¬((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) ↔ ((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) ↔ ((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) ↔ ((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) ↔ ((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) ↔ ((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) ↔ ((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) ↔ ((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) ↔ ((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 1), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : n > 1), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : n > 1), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : n > 1), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : n > 1), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : n > 1), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : n > 1), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : n > 1), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 0) ↔ (n > 1) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 0) ↔ (n > 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 0) ↔ (n > 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 0) ↔ (n > 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 0) ↔ (n > 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 0) ↔ (n > 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 0) ↔ (n > 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 0) ↔ (n > 1))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 0) ↔ (n > 1))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 0) ↔ (n > 1))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 0) ↔ (n > 1))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 0) ↔ (n > 1))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 0) ↔ (n > 1))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 0) ↔ (n > 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 0) ↔ (n > 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 0) ↔ (n > 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 0) ↔ (n > 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 0) ↔ (n > 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 0) ↔ (n > 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 1), (a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), (a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), (a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), (a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), (a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), (a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), (a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), (a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : n ≥ 1), (a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : n ≥ 1), (a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : n ≥ 1), (a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : n ≥ 1), (a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : n ≥ 1), (a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : n ≥ 1), (a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) →
    (∀ (n : ℕ) (hn : n ≥ 1), (a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n > 0) ∧ (¬((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n > 0) ∧ (¬((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n > 0) ∧ (¬((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n > 0) ∧ (¬((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n > 0) ∧ (¬((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n > 0) ∧ (¬((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n > 0) ∧ (¬((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n > 0) ∧ (¬((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) ↔ ((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) ↔ ((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) ↔ ((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) ↔ ((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) ↔ ((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) ↔ ((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) ↔ ((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)) ↔ ((a n : ℝ) =
      (⌊ 1 / ((5 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : n > 0) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : n > 0) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : n > 0) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : n > 0) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : n > 0) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
