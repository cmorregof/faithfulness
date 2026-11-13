import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 1209

*References:*
- [erdosproblems.com/429](https://www.erdosproblems.com/429)
- [erdosproblems.com/1102](https://www.erdosproblems.com/1102)
- [erdosproblems.com/1209](https://www.erdosproblems.com/1209)
- [Er80] Erdős, Paul, A survey of problems in combinatorial number theory. Ann. Discrete Math.
  (1980), 89-115.
-/

section

open Nat Set

namespace Erdos1209

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m : ℕ) (hk : 1 < k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) →
    (∀ (k m : ℕ) (hk : 1 < k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) →
    (∀ (k m : ℕ) (hk : 1 < k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) →
    (∀ (k m : ℕ) (hk : 1 < k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) →
    (∀ (k m : ℕ) (hk : 1 < k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) →
    (∀ (k m : ℕ) (hk : 1 < k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) →
    (∀ (k m : ℕ) (hk : 1 < k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) →
    (∀ (k m : ℕ) (hk : 1 < k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k m : ℕ)  :
    (1 ≤ k) ↔ (1 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (k m : ℕ)  :
    (1 ≤ k) ↔ (1 < k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k m : ℕ)  :
    (1 ≤ k) ↔ (1 < k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k m : ℕ)  :
    (1 ≤ k) ↔ (1 < k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k m : ℕ)  :
    (1 ≤ k) ↔ (1 < k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k m : ℕ)  :
    (1 ≤ k) ↔ (1 < k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k m : ℕ)  :
    (1 ≤ k) ↔ (1 < k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (1 < k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (1 < k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (1 < k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (1 < k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (1 < k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (1 < k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m : ℕ) (hk : k ≥ 1), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) ↔
    (∀ (k m : ℕ) (hk : k ≥ 1), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) ↔
    (∀ (k m : ℕ) (hk : k ≥ 1), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) ↔
    (∀ (k m : ℕ) (hk : k ≥ 1), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) ↔
    (∀ (k m : ℕ) (hk : k ≥ 1), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p₁, m < p₁ ∧ p₁.Prime ∧ ¬ (k + p₁).Prime

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) ↔ (∃ p₁, m < p₁ ∧ p₁.Prime ∧ ¬ (k + p₁).Prime) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) ↔ (∃ p₁, m < p₁ ∧ p₁.Prime ∧ ¬ (k + p₁).Prime) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) ↔ (∃ p₁, m < p₁ ∧ p₁.Prime ∧ ¬ (k + p₁).Prime) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) ↔ (∃ p₁, m < p₁ ∧ p₁.Prime ∧ ¬ (k + p₁).Prime) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) ↔ (∃ p₁, m < p₁ ∧ p₁.Prime ∧ ¬ (k + p₁).Prime) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) ↔ (∃ p₁, m < p₁ ∧ p₁.Prime ∧ ¬ (k + p₁).Prime) := by
  omega

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) ↔ (∃ p₁, m < p₁ ∧ p₁.Prime ∧ ¬ (k + p₁).Prime) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) ↔ (∃ p₁, m < p₁ ∧ p₁.Prime ∧ ¬ (k + p₁).Prime) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) ↔
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p₁, m < p₁ ∧ p₁.Prime ∧ ¬ (k + p₁).Prime) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) ↔
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p₁, m < p₁ ∧ p₁.Prime ∧ ¬ (k + p₁).Prime) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) ↔
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p₁, m < p₁ ∧ p₁.Prime ∧ ¬ (k + p₁).Prime) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) ↔
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p₁, m < p₁ ∧ p₁.Prime ∧ ¬ (k + p₁).Prime) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m : ℕ) (hk₀ : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) ↔
    (∀ (k m : ℕ) (hk₀ : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) ↔
    (∀ (k m : ℕ) (hk₀ : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) ↔
    (∀ (k m : ℕ) (hk₀ : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) ↔
    (∀ (k m : ℕ) (hk₀ : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m : ℕ) (hk : ¬(k < 1)), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  omega

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) ↔
    (∀ (k m : ℕ) (hk : ¬(k < 1)), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) ↔
    (∀ (k m : ℕ) (hk : ¬(k < 1)), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) ↔
    (∀ (k m : ℕ) (hk : ¬(k < 1)), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) ↔
    (∀ (k m : ℕ) (hk : ¬(k < 1)), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m : ℕ) (hk : 0 < k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (0 < k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (0 < k) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (0 < k) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (0 < k) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (0 < k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (0 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (0 < k) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (0 < k) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) ↔
    (∀ (k m : ℕ) (hk : 0 < k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) ↔
    (∀ (k m : ℕ) (hk : 0 < k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) ↔
    (∀ (k m : ℕ) (hk : 0 < k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) ↔
    (∀ (k m : ℕ) (hk : 0 < k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m : ℕ) (hk : k > 1), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) →
    (∀ (k m : ℕ) (hk : k > 1), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) →
    (∀ (k m : ℕ) (hk : k > 1), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) →
    (∀ (k m : ℕ) (hk : k > 1), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) →
    (∀ (k m : ℕ) (hk : k > 1), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) →
    (∀ (k m : ℕ) (hk : k > 1), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) →
    (∀ (k m : ℕ) (hk : k > 1), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) →
    (∀ (k m : ℕ) (hk : k > 1), ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k m : ℕ)  :
    (1 ≤ k) ↔ (k > 1) := by
  omega

set_option maxHeartbeats 200000 in
example (k m : ℕ)  :
    (1 ≤ k) ↔ (k > 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k m : ℕ)  :
    (1 ≤ k) ↔ (k > 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k m : ℕ)  :
    (1 ≤ k) ↔ (k > 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k m : ℕ)  :
    (1 ≤ k) ↔ (k > 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k m : ℕ)  :
    (1 ≤ k) ↔ (k > 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k m : ℕ)  :
    (1 ≤ k) ↔ (k > 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (k > 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (k > 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (k > 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (k > 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (k > 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (k > 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (k m : ℕ) (hk : 1 ≤ k) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (k m : ℕ) (hk : 1 ≤ k) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (k m : ℕ) (hk : 1 ≤ k) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (k m : ℕ) (hk : 1 ≤ k) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (k m : ℕ) (hk : 1 ≤ k) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
