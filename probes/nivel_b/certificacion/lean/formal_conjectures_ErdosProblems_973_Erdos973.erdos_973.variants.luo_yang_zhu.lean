import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 973

*References:*
- [erdosproblems.com/973](https://www.erdosproblems.com/973)
- [Er92f] Erdős, L., On some problems of {P}. Turán concerning power sums of
  complex numbers. Acta Math. Hungar. (1992), 11--24.
- [Ha74] Hayman, W. K., Research problems in function theory: new problems. (1974), 155--180.
- [LYZ26] Luo, Yanping and Yang, Ruiyi and Zhu, Keheng, Exterior power sums.
  [arxiv/2607.22017](https://arxiv.org/abs/2607.22017)
- [TWHC26] Tan, Xiaojun and Wang, Qihang and Huang, Wei and Chen, Kun, Residual bounds for
  Schur-stable polynomials. [arxiv/2608.02043](https://arxiv.org/abs/2608.02043)
- [Tu84b] Turán, Paul, On a new method of analysis and its applications. (1984), xvi+584.
- [PALOMAR-2026-09-20-000008](https://palomar-registry.org/entry.html?id=PALOMAR-2026-09-20-000008&version=1)
-/

section

open Finset Filter

namespace Erdos973

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (lam : ℝ) (hlam : 0 ≤ lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 ≤ lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) →
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 ≤ lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) →
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 ≤ lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) →
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 ≤ lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) →
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 ≤ lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) →
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 ≤ lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) →
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 ≤ lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) →
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (lam : ℝ)  :
    (0 < lam) ↔ (0 ≤ lam) := by
  omega

set_option maxHeartbeats 200000 in
example (lam : ℝ)  :
    (0 < lam) ↔ (0 ≤ lam) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (lam : ℝ)  :
    (0 < lam) ↔ (0 ≤ lam) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (lam : ℝ)  :
    (0 < lam) ↔ (0 ≤ lam) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (lam : ℝ)  :
    (0 < lam) ↔ (0 ≤ lam) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (lam : ℝ)  :
    (0 < lam) ↔ (0 ≤ lam) := by
  simp_all

set_option maxHeartbeats 200000 in
example (lam : ℝ)  :
    (0 < lam) ↔ (0 ≤ lam) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), (¬((0 < lam) ↔ (0 ≤ lam))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), (¬((0 < lam) ↔ (0 ≤ lam))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), (¬((0 < lam) ↔ (0 ≤ lam))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), (¬((0 < lam) ↔ (0 ≤ lam))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), (¬((0 < lam) ↔ (0 ≤ lam))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), (¬((0 < lam) ↔ (0 ≤ lam))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), ¬((0 < lam) ↔ (0 ≤ lam)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), ¬((0 < lam) ↔ (0 ≤ lam)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), ¬((0 < lam) ↔ (0 ≤ lam)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), ¬((0 < lam) ↔ (0 ≤ lam)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), ¬((0 < lam) ↔ (0 ≤ lam)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), ¬((0 < lam) ↔ (0 ≤ lam)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) →
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) →
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) →
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) →
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) →
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) →
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) →
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) →
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) →
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) →
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) →
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) →
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) →
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) →
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), (0 < lam) ∧ (¬(∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), (0 < lam) ∧ (¬(∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), (0 < lam) ∧ (¬(∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), (0 < lam) ∧ (¬(∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), (0 < lam) ∧ (¬(∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), (0 < lam) ∧ (¬(∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖)) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), (0 < lam) ∧ (¬(∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), ¬((∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔ (∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), ¬((∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔ (∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), ¬((∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔ (∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), ¬((∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔ (∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), ¬((∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔ (∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖)) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), ¬((∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔ (∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), ¬((∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔ (∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (lam : ℝ) (hlam : lam > 0), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖

set_option maxHeartbeats 200000 in
example (lam : ℝ) :
    (0 < lam) ↔ (lam > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (lam : ℝ) :
    (0 < lam) ↔ (lam > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (lam : ℝ) :
    (0 < lam) ↔ (lam > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (lam : ℝ) :
    (0 < lam) ↔ (lam > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (lam : ℝ) :
    (0 < lam) ↔ (lam > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (lam : ℝ) :
    (0 < lam) ↔ (lam > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (lam : ℝ) :
    (0 < lam) ↔ (lam > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (lam : ℝ) :
    (0 < lam) ↔ (lam > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔
    (∀ (lam : ℝ) (hlam : lam > 0), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔
    (∀ (lam : ℝ) (hlam : lam > 0), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔
    (∀ (lam : ℝ) (hlam : lam > 0), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔
    (∀ (lam : ℝ) (hlam : lam > 0), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z₁ : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z₁ i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z₁ i ^ k‖

set_option maxHeartbeats 200000 in
example (lam : ℝ) :
    (∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔ (∀ᶠ n in atTop, ∀ z₁ : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z₁ i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z₁ i ^ k‖) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (lam : ℝ) :
    (∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔ (∀ᶠ n in atTop, ∀ z₁ : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z₁ i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z₁ i ^ k‖) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (lam : ℝ) :
    (∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔ (∀ᶠ n in atTop, ∀ z₁ : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z₁ i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z₁ i ^ k‖) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (lam : ℝ) :
    (∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔ (∀ᶠ n in atTop, ∀ z₁ : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z₁ i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z₁ i ^ k‖) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (lam : ℝ) :
    (∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔ (∀ᶠ n in atTop, ∀ z₁ : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z₁ i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z₁ i ^ k‖) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (lam : ℝ) :
    (∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔ (∀ᶠ n in atTop, ∀ z₁ : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z₁ i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z₁ i ^ k‖) := by
  omega

set_option maxHeartbeats 200000 in
example (lam : ℝ) :
    (∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔ (∀ᶠ n in atTop, ∀ z₁ : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z₁ i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z₁ i ^ k‖) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (lam : ℝ) :
    (∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔ (∀ᶠ n in atTop, ∀ z₁ : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z₁ i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z₁ i ^ k‖) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z₁ : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z₁ i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z₁ i ^ k‖) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z₁ : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z₁ i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z₁ i ^ k‖) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z₁ : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z₁ i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z₁ i ^ k‖) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z₁ : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z₁ i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z₁ i ^ k‖) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i, 1 ≤ i ∧ i ≤ n → 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖

set_option maxHeartbeats 200000 in
example (lam : ℝ) :
    (∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔ (∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i, 1 ≤ i ∧ i ≤ n → 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (lam : ℝ) :
    (∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔ (∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i, 1 ≤ i ∧ i ≤ n → 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (lam : ℝ) :
    (∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔ (∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i, 1 ≤ i ∧ i ≤ n → 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (lam : ℝ) :
    (∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔ (∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i, 1 ≤ i ∧ i ≤ n → 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (lam : ℝ) :
    (∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔ (∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i, 1 ≤ i ∧ i ≤ n → 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (lam : ℝ) :
    (∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔ (∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i, 1 ≤ i ∧ i ≤ n → 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  omega

set_option maxHeartbeats 200000 in
example (lam : ℝ) :
    (∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔ (∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i, 1 ≤ i ∧ i ≤ n → 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (lam : ℝ) :
    (∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔ (∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i, 1 ≤ i ∧ i ≤ n → 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i, 1 ≤ i ∧ i ≤ n → 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i, 1 ≤ i ∧ i ≤ n → 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i, 1 ≤ i ∧ i ≤ n → 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i, 1 ≤ i ∧ i ≤ n → 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (lam : ℝ) (hlam₀ : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔
    (∀ (lam : ℝ) (hlam₀ : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔
    (∀ (lam : ℝ) (hlam₀ : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔
    (∀ (lam : ℝ) (hlam₀ : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔
    (∀ (lam : ℝ) (hlam₀ : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (lam : ℝ) (hlam : ¬(lam ≤ 0)), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖

set_option maxHeartbeats 200000 in
example (lam : ℝ) :
    (0 < lam) ↔ (¬(lam ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (lam : ℝ) :
    (0 < lam) ↔ (¬(lam ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (lam : ℝ) :
    (0 < lam) ↔ (¬(lam ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (lam : ℝ) :
    (0 < lam) ↔ (¬(lam ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (lam : ℝ) :
    (0 < lam) ↔ (¬(lam ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (lam : ℝ) :
    (0 < lam) ↔ (¬(lam ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (lam : ℝ) :
    (0 < lam) ↔ (¬(lam ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (lam : ℝ) :
    (0 < lam) ↔ (¬(lam ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔
    (∀ (lam : ℝ) (hlam : ¬(lam ≤ 0)), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔
    (∀ (lam : ℝ) (hlam : ¬(lam ≤ 0)), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔
    (∀ (lam : ℝ) (hlam : ¬(lam ≤ 0)), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔
    (∀ (lam : ℝ) (hlam : ¬(lam ≤ 0)), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (lam : ℝ) (hlam : lam ≥ 0), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : lam ≥ 0), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) →
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : lam ≥ 0), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) →
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : lam ≥ 0), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) →
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : lam ≥ 0), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) →
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : lam ≥ 0), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) →
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : lam ≥ 0), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) →
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : lam ≥ 0), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) →
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (lam : ℝ)  :
    (0 < lam) ↔ (lam ≥ 0) := by
  omega

set_option maxHeartbeats 200000 in
example (lam : ℝ)  :
    (0 < lam) ↔ (lam ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (lam : ℝ)  :
    (0 < lam) ↔ (lam ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (lam : ℝ)  :
    (0 < lam) ↔ (lam ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (lam : ℝ)  :
    (0 < lam) ↔ (lam ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (lam : ℝ)  :
    (0 < lam) ↔ (lam ≥ 0) := by
  simp_all

set_option maxHeartbeats 200000 in
example (lam : ℝ)  :
    (0 < lam) ↔ (lam ≥ 0) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), (¬((0 < lam) ↔ (lam ≥ 0))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), (¬((0 < lam) ↔ (lam ≥ 0))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), (¬((0 < lam) ↔ (lam ≥ 0))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), (¬((0 < lam) ↔ (lam ≥ 0))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), (¬((0 < lam) ↔ (lam ≥ 0))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), (¬((0 < lam) ↔ (lam ≥ 0))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), ¬((0 < lam) ↔ (lam ≥ 0)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), ¬((0 < lam) ↔ (lam ≥ 0)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), ¬((0 < lam) ↔ (lam ≥ 0)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), ¬((0 < lam) ↔ (lam ≥ 0)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), ¬((0 < lam) ↔ (lam ≥ 0)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), ¬((0 < lam) ↔ (lam ≥ 0)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (lam : ℝ) (hlam : lam > 0), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : lam > 0), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) →
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : lam > 0), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) →
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : lam > 0), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) →
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : lam > 0), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) →
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : lam > 0), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) →
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : lam > 0), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) →
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : lam > 0), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) →
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) →
    (∀ (lam : ℝ) (hlam : lam > 0), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) →
    (∀ (lam : ℝ) (hlam : lam > 0), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) →
    (∀ (lam : ℝ) (hlam : lam > 0), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) →
    (∀ (lam : ℝ) (hlam : lam > 0), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) →
    (∀ (lam : ℝ) (hlam : lam > 0), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) →
    (∀ (lam : ℝ) (hlam : lam > 0), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 0 < lam), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) →
    (∀ (lam : ℝ) (hlam : lam > 0), ∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), (0 < lam) ∧ (¬(∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), (0 < lam) ∧ (¬(∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), (0 < lam) ∧ (¬(∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), (0 < lam) ∧ (¬(∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), (0 < lam) ∧ (¬(∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), (0 < lam) ∧ (¬(∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖)) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), (0 < lam) ∧ (¬(∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), ¬((∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔ (∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), ¬((∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔ (∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), ¬((∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔ (∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), ¬((∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔ (∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), ¬((∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔ (∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖)) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), ¬((∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔ (∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), ¬((∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖) ↔ (∀ᶠ n in atTop, ∀ z : ℕ → ℂ,
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 3 (n + 1),
        Real.exp (-lam * n) < ‖∑ i ∈ Icc 1 n, z i ^ k‖)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (lam : ℝ) (hlam : 0 < lam) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (lam : ℝ) (hlam : 0 < lam) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (lam : ℝ) (hlam : 0 < lam) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (lam : ℝ) (hlam : 0 < lam) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (lam : ℝ) (hlam : 0 < lam) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
