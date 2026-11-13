import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 727

*Reference:* [erdosproblems.com/727](https://www.erdosproblems.com/727)
-/

section

open scoped Nat

namespace Erdos727

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) →
    (∀ (k : ℕ) (hk : 3 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) →
    (∀ (k : ℕ) (hk : 3 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) →
    (∀ (k : ℕ) (hk : 3 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) →
    (∀ (k : ℕ) (hk : 3 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) →
    (∀ (k : ℕ) (hk : 3 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) →
    (∀ (k : ℕ) (hk : 3 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) →
    (∀ (k : ℕ) (hk : 3 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (3 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (3 ≤ k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (3 ≤ k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 2), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (k ≥ 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (k ≥ 2) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (k ≥ 2) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (k ≥ 2) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (k ≥ 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (k ≥ 2) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (k ≥ 2) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (k ≥ 2) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) ↔
    (∀ (k : ℕ) (hk : k ≥ 2), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) ↔
    (∀ (k : ℕ) (hk : k ≥ 2), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) ↔
    (∀ (k : ℕ) (hk : k ≥ 2), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) ↔
    (∀ (k : ℕ) (hk : k ≥ 2), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk₀ : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) ↔
    (∀ (k : ℕ) (hk₀ : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) ↔
    (∀ (k : ℕ) (hk₀ : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) ↔
    (∀ (k : ℕ) (hk₀ : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) ↔
    (∀ (k : ℕ) (hk₀ : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : ¬(k < 2)), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (¬(k < 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (¬(k < 2)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (¬(k < 2)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (¬(k < 2)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (¬(k < 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (¬(k < 2)) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (¬(k < 2)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (¬(k < 2)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) ↔
    (∀ (k : ℕ) (hk : ¬(k < 2)), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) ↔
    (∀ (k : ℕ) (hk : ¬(k < 2)), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) ↔
    (∀ (k : ℕ) (hk : ¬(k < 2)), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) ↔
    (∀ (k : ℕ) (hk : ¬(k < 2)), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 < k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (1 < k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (1 < k) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (1 < k) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (1 < k) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (1 < k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (1 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (1 < k) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (1 < k) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) ↔
    (∀ (k : ℕ) (hk : 1 < k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) ↔
    (∀ (k : ℕ) (hk : 1 < k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) ↔
    (∀ (k : ℕ) (hk : 1 < k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) ↔
    (∀ (k : ℕ) (hk : 1 < k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 3), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) →
    (∀ (k : ℕ) (hk : k ≥ 3), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) →
    (∀ (k : ℕ) (hk : k ≥ 3), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) →
    (∀ (k : ℕ) (hk : k ≥ 3), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) →
    (∀ (k : ℕ) (hk : k ≥ 3), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) →
    (∀ (k : ℕ) (hk : k ≥ 3), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) →
    (∀ (k : ℕ) (hk : k ≥ 3), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) →
    (∀ (k : ℕ) (hk : k ≥ 3), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (k ≥ 3) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (k ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (k ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (k ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (k ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (k ≥ 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (k ≥ 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (k ≥ 3))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (k ≥ 3))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (k ≥ 3))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (k ≥ 3))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (k ≥ 3))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (k ≥ 3))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (k ≥ 3))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k ≥ 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k ≥ 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k ≥ 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k ≥ 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k ≥ 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k ≥ 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k ≥ 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 < k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (3 * n)}

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 < k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (3 * n)}) →
    (∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 < k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (3 * n)}) →
    (∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 < k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (3 * n)}) →
    (∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 < k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (3 * n)}) →
    (∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 < k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (3 * n)}) →
    (∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 < k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (3 * n)}) →
    (∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 < k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (3 * n)}) →
    (∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) →
    (∀ (k : ℕ) (hk : 1 < k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (3 * n)}) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) →
    (∀ (k : ℕ) (hk : 1 < k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (3 * n)}) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) →
    (∀ (k : ℕ) (hk : 1 < k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (3 * n)}) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) →
    (∀ (k : ℕ) (hk : 1 < k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (3 * n)}) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) →
    (∀ (k : ℕ) (hk : 1 < k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (3 * n)}) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) →
    (∀ (k : ℕ) (hk : 1 < k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (3 * n)}) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) →
    (∀ (k : ℕ) (hk : 1 < k), Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (3 * n)}) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (2 ≤ k) ∧ (¬(Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (3 * n)})) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (2 ≤ k) ∧ (¬(Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (3 * n)})) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (2 ≤ k) ∧ (¬(Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (3 * n)})) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (2 ≤ k) ∧ (¬(Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (3 * n)})) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (2 ≤ k) ∧ (¬(Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (3 * n)})) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (2 ≤ k) ∧ (¬(Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (3 * n)})) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (2 ≤ k) ∧ (¬(Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (3 * n)})) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) ↔ (Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (3 * n)})) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) ↔ (Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (3 * n)})) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) ↔ (Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (3 * n)})) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) ↔ (Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (3 * n)})) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) ↔ (Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (3 * n)})) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) ↔ (Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (3 * n)})) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (2 * n)}) ↔ (Set.Infinite {n : ℕ |
      (Nat.factorial (n + k)) * (Nat.factorial (n + 1)) ∣ Nat.factorial (3 * n)})) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 2 ≤ k) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 2 ≤ k) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 2 ≤ k) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 2 ≤ k) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 2 ≤ k) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
