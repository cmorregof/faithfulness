import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 124

*References:*
- [erdosproblems.com/124](https://www.erdosproblems.com/124)
- [BEGL96] Burr, S. A. and Erdős, P. and Graham, R. L. and Li, W. Wen-Ching, Complete sequences of sets of integer powers. Acta Arith. (1996), 133-138.
-/

section

open Filter
open scoped Pointwise

namespace Erdos124

/-- The set of integers which are the sum of distinct powers `d ^ i` with `i ≥ k`. -/
def sumsOfDistinctPowers (d k : ℕ) : Set ℕ :=
  {x | ∃ s : Finset ℕ, (∀ i ∈ s, k ≤ i) ∧ ∑ i ∈ s, d ^ i = x}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {ε : ℝ} (hε : 0 ≤ ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : 0 ≤ ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) →
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : 0 ≤ ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) →
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : 0 ≤ ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) →
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : 0 ≤ ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) →
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : 0 ≤ ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) →
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : 0 ≤ ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) →
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : 0 ≤ ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) →
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {ε : ℝ}  :
    (0 < ε) ↔ (0 ≤ ε) := by
  omega

set_option maxHeartbeats 200000 in
example {ε : ℝ}  :
    (0 < ε) ↔ (0 ≤ ε) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {ε : ℝ}  :
    (0 < ε) ↔ (0 ≤ ε) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {ε : ℝ}  :
    (0 < ε) ↔ (0 ≤ ε) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {ε : ℝ}  :
    (0 < ε) ↔ (0 ≤ ε) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {ε : ℝ}  :
    (0 < ε) ↔ (0 ≤ ε) := by
  simp_all

set_option maxHeartbeats 200000 in
example {ε : ℝ}  :
    (0 < ε) ↔ (0 ≤ ε) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (0 ≤ ε)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (0 ≤ ε)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (0 ≤ ε)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (0 ≤ ε)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (0 ≤ ε)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (0 ≤ ε)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) →
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) →
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) →
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) →
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) →
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) →
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) →
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) →
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) →
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) →
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) →
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) →
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) →
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) →
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n)) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) ↔ (∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) ↔ (∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) ↔ (∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) ↔ (∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) ↔ (∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) ↔ (∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n)) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) ↔ (∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {ε : ℝ} (hε : ε > 0), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n

set_option maxHeartbeats 200000 in
example {ε : ℝ} :
    (0 < ε) ↔ (ε > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {ε : ℝ} :
    (0 < ε) ↔ (ε > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {ε : ℝ} :
    (0 < ε) ↔ (ε > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {ε : ℝ} :
    (0 < ε) ↔ (ε > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {ε : ℝ} :
    (0 < ε) ↔ (ε > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {ε : ℝ} :
    (0 < ε) ↔ (ε > 0) := by
  omega

set_option maxHeartbeats 200000 in
example {ε : ℝ} :
    (0 < ε) ↔ (ε > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {ε : ℝ} :
    (0 < ε) ↔ (ε > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) ↔
    (∀ {ε : ℝ} (hε : ε > 0), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) ↔
    (∀ {ε : ℝ} (hε : ε > 0), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) ↔
    (∀ {ε : ℝ} (hε : ε > 0), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) ↔
    (∀ {ε : ℝ} (hε : ε > 0), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {ε : ℝ} (hε : 0 < ε), ∃ d₁ : ℕ → ℕ, StrictMono d₁ ∧ 2 ≤ d₁ 0 ∧
      Summable (fun i ↦ (d₁ i - 1 : ℝ)⁻¹) ∧ ∑' i, (d₁ i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d₁ i) k) ∧
        ∑ i ∈ I, a i = n

set_option maxHeartbeats 200000 in
example {ε : ℝ} :
    (∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) ↔ (∃ d₁ : ℕ → ℕ, StrictMono d₁ ∧ 2 ≤ d₁ 0 ∧
      Summable (fun i ↦ (d₁ i - 1 : ℝ)⁻¹) ∧ ∑' i, (d₁ i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d₁ i) k) ∧
        ∑ i ∈ I, a i = n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {ε : ℝ} :
    (∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) ↔ (∃ d₁ : ℕ → ℕ, StrictMono d₁ ∧ 2 ≤ d₁ 0 ∧
      Summable (fun i ↦ (d₁ i - 1 : ℝ)⁻¹) ∧ ∑' i, (d₁ i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d₁ i) k) ∧
        ∑ i ∈ I, a i = n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {ε : ℝ} :
    (∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) ↔ (∃ d₁ : ℕ → ℕ, StrictMono d₁ ∧ 2 ≤ d₁ 0 ∧
      Summable (fun i ↦ (d₁ i - 1 : ℝ)⁻¹) ∧ ∑' i, (d₁ i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d₁ i) k) ∧
        ∑ i ∈ I, a i = n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {ε : ℝ} :
    (∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) ↔ (∃ d₁ : ℕ → ℕ, StrictMono d₁ ∧ 2 ≤ d₁ 0 ∧
      Summable (fun i ↦ (d₁ i - 1 : ℝ)⁻¹) ∧ ∑' i, (d₁ i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d₁ i) k) ∧
        ∑ i ∈ I, a i = n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {ε : ℝ} :
    (∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) ↔ (∃ d₁ : ℕ → ℕ, StrictMono d₁ ∧ 2 ≤ d₁ 0 ∧
      Summable (fun i ↦ (d₁ i - 1 : ℝ)⁻¹) ∧ ∑' i, (d₁ i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d₁ i) k) ∧
        ∑ i ∈ I, a i = n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {ε : ℝ} :
    (∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) ↔ (∃ d₁ : ℕ → ℕ, StrictMono d₁ ∧ 2 ≤ d₁ 0 ∧
      Summable (fun i ↦ (d₁ i - 1 : ℝ)⁻¹) ∧ ∑' i, (d₁ i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d₁ i) k) ∧
        ∑ i ∈ I, a i = n) := by
  omega

set_option maxHeartbeats 200000 in
example {ε : ℝ} :
    (∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) ↔ (∃ d₁ : ℕ → ℕ, StrictMono d₁ ∧ 2 ≤ d₁ 0 ∧
      Summable (fun i ↦ (d₁ i - 1 : ℝ)⁻¹) ∧ ∑' i, (d₁ i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d₁ i) k) ∧
        ∑ i ∈ I, a i = n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {ε : ℝ} :
    (∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) ↔ (∃ d₁ : ℕ → ℕ, StrictMono d₁ ∧ 2 ≤ d₁ 0 ∧
      Summable (fun i ↦ (d₁ i - 1 : ℝ)⁻¹) ∧ ∑' i, (d₁ i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d₁ i) k) ∧
        ∑ i ∈ I, a i = n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) ↔
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d₁ : ℕ → ℕ, StrictMono d₁ ∧ 2 ≤ d₁ 0 ∧
      Summable (fun i ↦ (d₁ i - 1 : ℝ)⁻¹) ∧ ∑' i, (d₁ i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d₁ i) k) ∧
        ∑ i ∈ I, a i = n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) ↔
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d₁ : ℕ → ℕ, StrictMono d₁ ∧ 2 ≤ d₁ 0 ∧
      Summable (fun i ↦ (d₁ i - 1 : ℝ)⁻¹) ∧ ∑' i, (d₁ i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d₁ i) k) ∧
        ∑ i ∈ I, a i = n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) ↔
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d₁ : ℕ → ℕ, StrictMono d₁ ∧ 2 ≤ d₁ 0 ∧
      Summable (fun i ↦ (d₁ i - 1 : ℝ)⁻¹) ∧ ∑' i, (d₁ i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d₁ i) k) ∧
        ∑ i ∈ I, a i = n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) ↔
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d₁ : ℕ → ℕ, StrictMono d₁ ∧ 2 ≤ d₁ 0 ∧
      Summable (fun i ↦ (d₁ i - 1 : ℝ)⁻¹) ∧ ∑' i, (d₁ i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d₁ i) k) ∧
        ∑ i ∈ I, a i = n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {ε : ℝ} (hε₀ : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) ↔
    (∀ {ε : ℝ} (hε₀ : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) ↔
    (∀ {ε : ℝ} (hε₀ : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) ↔
    (∀ {ε : ℝ} (hε₀ : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) ↔
    (∀ {ε : ℝ} (hε₀ : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {ε : ℝ} (hε : ¬(ε ≤ 0)), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n

set_option maxHeartbeats 200000 in
example {ε : ℝ} :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {ε : ℝ} :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {ε : ℝ} :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {ε : ℝ} :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {ε : ℝ} :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {ε : ℝ} :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example {ε : ℝ} :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {ε : ℝ} :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) ↔
    (∀ {ε : ℝ} (hε : ¬(ε ≤ 0)), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) ↔
    (∀ {ε : ℝ} (hε : ¬(ε ≤ 0)), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) ↔
    (∀ {ε : ℝ} (hε : ¬(ε ≤ 0)), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) ↔
    (∀ {ε : ℝ} (hε : ¬(ε ≤ 0)), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {ε : ℝ} (hε : ε ≥ 0), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : ε ≥ 0), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) →
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : ε ≥ 0), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) →
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : ε ≥ 0), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) →
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : ε ≥ 0), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) →
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : ε ≥ 0), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) →
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : ε ≥ 0), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) →
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : ε ≥ 0), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) →
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {ε : ℝ}  :
    (0 < ε) ↔ (ε ≥ 0) := by
  omega

set_option maxHeartbeats 200000 in
example {ε : ℝ}  :
    (0 < ε) ↔ (ε ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {ε : ℝ}  :
    (0 < ε) ↔ (ε ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {ε : ℝ}  :
    (0 < ε) ↔ (ε ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {ε : ℝ}  :
    (0 < ε) ↔ (ε ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {ε : ℝ}  :
    (0 < ε) ↔ (ε ≥ 0) := by
  simp_all

set_option maxHeartbeats 200000 in
example {ε : ℝ}  :
    (0 < ε) ↔ (ε ≥ 0) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (ε ≥ 0)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (ε ≥ 0)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (ε ≥ 0)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (ε ≥ 0)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (ε ≥ 0)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (ε ≥ 0)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {ε : ℝ} (hε : ε > 0), ∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : ε > 0), ∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) →
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : ε > 0), ∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) →
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : ε > 0), ∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) →
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : ε > 0), ∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) →
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : ε > 0), ∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) →
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : ε > 0), ∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) →
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : ε > 0), ∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) →
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) →
    (∀ {ε : ℝ} (hε : ε > 0), ∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) →
    (∀ {ε : ℝ} (hε : ε > 0), ∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) →
    (∀ {ε : ℝ} (hε : ε > 0), ∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) →
    (∀ {ε : ℝ} (hε : ε > 0), ∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) →
    (∀ {ε : ℝ} (hε : ε > 0), ∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) →
    (∀ {ε : ℝ} (hε : ε > 0), ∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) →
    (∀ {ε : ℝ} (hε : ε > 0), ∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n)) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) ↔ (∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) ↔ (∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) ↔ (∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) ↔ (∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) ↔ (∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) ↔ (∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n)) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n) ↔ (∃ d : ℕ → ℕ, StrictMono d ∧ 3 ≤ d 0 ∧
      Summable (fun i ↦ (d i - 1 : ℝ)⁻¹) ∧ ∑' i, (d i - 1 : ℝ)⁻¹ ≤ ε ∧ ∀ k ≠ 0, ∀ᶠ n in atTop,
      ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ sumsOfDistinctPowers (d i) k) ∧
        ∑ i ∈ I, a i = n)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {ε : ℝ} (hε : 0 < ε) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {ε : ℝ} (hε : 0 < ε) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {ε : ℝ} (hε : 0 < ε) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {ε : ℝ} (hε : 0 < ε) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {ε : ℝ} (hε : 0 < ε) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
