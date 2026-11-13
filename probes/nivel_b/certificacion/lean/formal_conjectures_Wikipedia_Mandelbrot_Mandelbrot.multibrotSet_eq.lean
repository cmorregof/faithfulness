import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Conjectures about the Mandelbrot and Multibrot sets
This file adds three conjectures about the Mandelbrot and Multibrot sets:
- the *MLC conjecture*, stating that these sets are locally connected
- the *density of hyperbolicity* conjecture, stating that parameters with attracting cycles are
  dense in the Mandelbrot and Multibrot sets
- the conjecture that the boundaries of these sets have zero area.
The first two conjectures are related in that the former implies the latter.

*References:*
 - [Wikipedia](https://en.wikipedia.org/wiki/Mandelbrot_set#Local_connectivity)
 - [arxiv/math/9902155](https://arxiv.org/abs/math/9902155)
 - [mathoverflow/37229](https://mathoverflow.net/questions/37229/)
-/

section

open Topology Set Function Filter Bornology Metric MeasureTheory

namespace Mandelbrot

/-- The Multibrot set of power `n` is the set of all parameters `c : ℂ` for which `0` does not
escape to infinity under repeated application of `z ↦ z ^ n + c`. -/
def multibrotSet (n : ℕ) : Set ℂ :=
  {c | ¬ Tendsto (fun k ↦ (fun z ↦ z ^ n + c)^[k] 0) atTop (cobounded ℂ)}

/-- The Mandelbrot set is the special case of the multibrot set for n = 2. In other words, it is the
set of all parameters `c : ℂ` for which `0` does not escape to infinity under repeated application
of `z ↦ z ^ 2 + c`. -/
abbrev mandelbrotSet := multibrotSet 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 3 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) →
    (∀ {n : ℕ} (hn : 3 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) →
    (∀ {n : ℕ} (hn : 3 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) →
    (∀ {n : ℕ} (hn : 3 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) →
    (∀ {n : ℕ} (hn : 3 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) →
    (∀ {n : ℕ} (hn : 3 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) →
    (∀ {n : ℕ} (hn : 3 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) →
    (∀ {n : ℕ} (hn : 3 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (2 ≤ n) ↔ (3 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (2 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (2 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (2 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (2 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (2 ≤ n) ↔ (3 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
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
  ∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : n ≥ 2), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (2 ≤ n) ↔ (n ≥ 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (2 ≤ n) ↔ (n ≥ 2) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (2 ≤ n) ↔ (n ≥ 2) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (2 ≤ n) ↔ (n ≥ 2) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (2 ≤ n) ↔ (n ≥ 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (2 ≤ n) ↔ (n ≥ 2) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (2 ≤ n) ↔ (n ≥ 2) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (2 ≤ n) ↔ (n ≥ 2) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) ↔
    (∀ {n : ℕ} (hn : n ≥ 2), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) ↔
    (∀ {n : ℕ} (hn : n ≥ 2), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) ↔
    (∀ {n : ℕ} (hn : n ≥ 2), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) ↔
    (∀ {n : ℕ} (hn : n ≥ 2), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k₁, ‖(fun z ↦ z ^ n + c)^[k₁] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) ↔ (multibrotSet n = {c | ∀ k₁, ‖(fun z ↦ z ^ n + c)^[k₁] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) ↔ (multibrotSet n = {c | ∀ k₁, ‖(fun z ↦ z ^ n + c)^[k₁] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) ↔ (multibrotSet n = {c | ∀ k₁, ‖(fun z ↦ z ^ n + c)^[k₁] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) ↔ (multibrotSet n = {c | ∀ k₁, ‖(fun z ↦ z ^ n + c)^[k₁] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) ↔ (multibrotSet n = {c | ∀ k₁, ‖(fun z ↦ z ^ n + c)^[k₁] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) ↔ (multibrotSet n = {c | ∀ k₁, ‖(fun z ↦ z ^ n + c)^[k₁] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) ↔ (multibrotSet n = {c | ∀ k₁, ‖(fun z ↦ z ^ n + c)^[k₁] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) ↔ (multibrotSet n = {c | ∀ k₁, ‖(fun z ↦ z ^ n + c)^[k₁] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) ↔
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k₁, ‖(fun z ↦ z ^ n + c)^[k₁] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) ↔
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k₁, ‖(fun z ↦ z ^ n + c)^[k₁] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) ↔
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k₁, ‖(fun z ↦ z ^ n + c)^[k₁] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) ↔
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k₁, ‖(fun z ↦ z ^ n + c)^[k₁] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn₀ : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) ↔
    (∀ {n : ℕ} (hn₀ : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) ↔
    (∀ {n : ℕ} (hn₀ : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) ↔
    (∀ {n : ℕ} (hn₀ : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) ↔
    (∀ {n : ℕ} (hn₀ : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : ¬(n < 2)), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) ↔
    (∀ {n : ℕ} (hn : ¬(n < 2)), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) ↔
    (∀ {n : ℕ} (hn : ¬(n < 2)), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) ↔
    (∀ {n : ℕ} (hn : ¬(n < 2)), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) ↔
    (∀ {n : ℕ} (hn : ¬(n < 2)), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 < n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (2 ≤ n) ↔ (1 < n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (2 ≤ n) ↔ (1 < n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (2 ≤ n) ↔ (1 < n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (2 ≤ n) ↔ (1 < n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (2 ≤ n) ↔ (1 < n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (2 ≤ n) ↔ (1 < n) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (2 ≤ n) ↔ (1 < n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (2 ≤ n) ↔ (1 < n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) ↔
    (∀ {n : ℕ} (hn : 1 < n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) ↔
    (∀ {n : ℕ} (hn : 1 < n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) ↔
    (∀ {n : ℕ} (hn : 1 < n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) ↔
    (∀ {n : ℕ} (hn : 1 < n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : n ≥ 3), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) →
    (∀ {n : ℕ} (hn : n ≥ 3), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) →
    (∀ {n : ℕ} (hn : n ≥ 3), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) →
    (∀ {n : ℕ} (hn : n ≥ 3), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) →
    (∀ {n : ℕ} (hn : n ≥ 3), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) →
    (∀ {n : ℕ} (hn : n ≥ 3), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) →
    (∀ {n : ℕ} (hn : n ≥ 3), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) →
    (∀ {n : ℕ} (hn : n ≥ 3), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (2 ≤ n) ↔ (n ≥ 3) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (2 ≤ n) ↔ (n ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (2 ≤ n) ↔ (n ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (2 ≤ n) ↔ (n ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (2 ≤ n) ↔ (n ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (2 ≤ n) ↔ (n ≥ 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
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
  ∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 < n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 3 ^ (n - 1 : ℝ)⁻¹}

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 3 ^ (n - 1 : ℝ)⁻¹}) →
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 3 ^ (n - 1 : ℝ)⁻¹}) →
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 3 ^ (n - 1 : ℝ)⁻¹}) →
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 3 ^ (n - 1 : ℝ)⁻¹}) →
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 3 ^ (n - 1 : ℝ)⁻¹}) →
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 3 ^ (n - 1 : ℝ)⁻¹}) →
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 3 ^ (n - 1 : ℝ)⁻¹}) →
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) →
    (∀ {n : ℕ} (hn : 1 < n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 3 ^ (n - 1 : ℝ)⁻¹}) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) →
    (∀ {n : ℕ} (hn : 1 < n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 3 ^ (n - 1 : ℝ)⁻¹}) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) →
    (∀ {n : ℕ} (hn : 1 < n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 3 ^ (n - 1 : ℝ)⁻¹}) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) →
    (∀ {n : ℕ} (hn : 1 < n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 3 ^ (n - 1 : ℝ)⁻¹}) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) →
    (∀ {n : ℕ} (hn : 1 < n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 3 ^ (n - 1 : ℝ)⁻¹}) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) →
    (∀ {n : ℕ} (hn : 1 < n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 3 ^ (n - 1 : ℝ)⁻¹}) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) →
    (∀ {n : ℕ} (hn : 1 < n), multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 3 ^ (n - 1 : ℝ)⁻¹}) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (2 ≤ n) ∧ (¬(multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 3 ^ (n - 1 : ℝ)⁻¹})) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (2 ≤ n) ∧ (¬(multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 3 ^ (n - 1 : ℝ)⁻¹})) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (2 ≤ n) ∧ (¬(multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 3 ^ (n - 1 : ℝ)⁻¹})) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (2 ≤ n) ∧ (¬(multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 3 ^ (n - 1 : ℝ)⁻¹})) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (2 ≤ n) ∧ (¬(multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 3 ^ (n - 1 : ℝ)⁻¹})) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (2 ≤ n) ∧ (¬(multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 3 ^ (n - 1 : ℝ)⁻¹})) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (2 ≤ n) ∧ (¬(multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 3 ^ (n - 1 : ℝ)⁻¹})) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) ↔ (multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 3 ^ (n - 1 : ℝ)⁻¹})) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) ↔ (multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 3 ^ (n - 1 : ℝ)⁻¹})) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) ↔ (multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 3 ^ (n - 1 : ℝ)⁻¹})) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) ↔ (multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 3 ^ (n - 1 : ℝ)⁻¹})) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) ↔ (multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 3 ^ (n - 1 : ℝ)⁻¹})) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) ↔ (multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 3 ^ (n - 1 : ℝ)⁻¹})) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 2 ^ (n - 1 : ℝ)⁻¹}) ↔ (multibrotSet n = {c | ∀ k, ‖(fun z ↦ z ^ n + c)^[k] 0‖ ≤ 3 ^ (n - 1 : ℝ)⁻¹})) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 2 ≤ n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 2 ≤ n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 2 ≤ n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 2 ≤ n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 2 ≤ n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
