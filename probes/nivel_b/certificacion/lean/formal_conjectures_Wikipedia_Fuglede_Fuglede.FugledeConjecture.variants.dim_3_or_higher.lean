import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Analysis.Fourier.SpectralSets
/-!
# Fuglede's conjecture in dimensions 1 and 2

*References:*
- [Fuglede's conjecture](https://en.wikipedia.org/wiki/Fuglede%27s_conjecture)
- [Zh26] [Zhang, Tao, *Both directions of Fuglede's conjecture fail in dimension two*,
  arXiv:2607.15632 (2026)](https://arxiv.org/abs/2607.15632)
-/

section

namespace Fuglede

open MeasureTheory

/--
**Fuglede's conjecture** in dimension `n`: A bounded subset of ℝ^n with positive Lebesgue measure is spectral iff it tiles ℝ^n by translation.
-/
def FugledeConjectureFor (n : ℕ) : Prop :=
  ∀ Ω : Set (Fin n → ℝ),
    Bornology.IsBounded Ω → MeasurableSet Ω → 0 < volume Ω →
      (isSpectral Ω ↔ tilesByTranslation Ω)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 < n), ¬ FugledeConjectureFor n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) →
    (∀ (n : ℕ) (hn : 3 < n), ¬ FugledeConjectureFor n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) →
    (∀ (n : ℕ) (hn : 3 < n), ¬ FugledeConjectureFor n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) →
    (∀ (n : ℕ) (hn : 3 < n), ¬ FugledeConjectureFor n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) →
    (∀ (n : ℕ) (hn : 3 < n), ¬ FugledeConjectureFor n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) →
    (∀ (n : ℕ) (hn : 3 < n), ¬ FugledeConjectureFor n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) →
    (∀ (n : ℕ) (hn : 3 < n), ¬ FugledeConjectureFor n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) →
    (∀ (n : ℕ) (hn : 3 < n), ¬ FugledeConjectureFor n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (3 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (3 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (3 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (3 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (3 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (3 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (3 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (3 < n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (3 < n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (3 < n))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (3 < n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (3 < n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (3 < n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (3 < n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (3 < n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (3 < n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (3 < n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (3 < n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (3 < n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (3 < n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (3 < n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 4 ≤ n), ¬ FugledeConjectureFor n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) →
    (∀ (n : ℕ) (hn : 4 ≤ n), ¬ FugledeConjectureFor n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) →
    (∀ (n : ℕ) (hn : 4 ≤ n), ¬ FugledeConjectureFor n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) →
    (∀ (n : ℕ) (hn : 4 ≤ n), ¬ FugledeConjectureFor n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) →
    (∀ (n : ℕ) (hn : 4 ≤ n), ¬ FugledeConjectureFor n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) →
    (∀ (n : ℕ) (hn : 4 ≤ n), ¬ FugledeConjectureFor n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) →
    (∀ (n : ℕ) (hn : 4 ≤ n), ¬ FugledeConjectureFor n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) →
    (∀ (n : ℕ) (hn : 4 ≤ n), ¬ FugledeConjectureFor n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (4 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (4 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (4 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (4 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (4 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (4 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (4 ≤ n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 3), ¬ FugledeConjectureFor n

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (n ≥ 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (n ≥ 3) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (n ≥ 3) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (n ≥ 3) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (n ≥ 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (n ≥ 3) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (n ≥ 3) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (n ≥ 3) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) ↔
    (∀ (n : ℕ) (hn : n ≥ 3), ¬ FugledeConjectureFor n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) ↔
    (∀ (n : ℕ) (hn : n ≥ 3), ¬ FugledeConjectureFor n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) ↔
    (∀ (n : ℕ) (hn : n ≥ 3), ¬ FugledeConjectureFor n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) ↔
    (∀ (n : ℕ) (hn : n ≥ 3), ¬ FugledeConjectureFor n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn₀ : 3 ≤ n), ¬ FugledeConjectureFor n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) ↔
    (∀ (n : ℕ) (hn₀ : 3 ≤ n), ¬ FugledeConjectureFor n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) ↔
    (∀ (n : ℕ) (hn₀ : 3 ≤ n), ¬ FugledeConjectureFor n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) ↔
    (∀ (n : ℕ) (hn₀ : 3 ≤ n), ¬ FugledeConjectureFor n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) ↔
    (∀ (n : ℕ) (hn₀ : 3 ≤ n), ¬ FugledeConjectureFor n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : ¬(n < 3)), ¬ FugledeConjectureFor n

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) ↔
    (∀ (n : ℕ) (hn : ¬(n < 3)), ¬ FugledeConjectureFor n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) ↔
    (∀ (n : ℕ) (hn : ¬(n < 3)), ¬ FugledeConjectureFor n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) ↔
    (∀ (n : ℕ) (hn : ¬(n < 3)), ¬ FugledeConjectureFor n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) ↔
    (∀ (n : ℕ) (hn : ¬(n < 3)), ¬ FugledeConjectureFor n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 < n), ¬ FugledeConjectureFor n

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (2 < n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (2 < n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (2 < n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (2 < n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (2 < n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (2 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) ↔
    (∀ (n : ℕ) (hn : 2 < n), ¬ FugledeConjectureFor n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) ↔
    (∀ (n : ℕ) (hn : 2 < n), ¬ FugledeConjectureFor n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) ↔
    (∀ (n : ℕ) (hn : 2 < n), ¬ FugledeConjectureFor n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) ↔
    (∀ (n : ℕ) (hn : 2 < n), ¬ FugledeConjectureFor n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 3), ¬ FugledeConjectureFor n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) →
    (∀ (n : ℕ) (hn : n > 3), ¬ FugledeConjectureFor n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) →
    (∀ (n : ℕ) (hn : n > 3), ¬ FugledeConjectureFor n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) →
    (∀ (n : ℕ) (hn : n > 3), ¬ FugledeConjectureFor n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) →
    (∀ (n : ℕ) (hn : n > 3), ¬ FugledeConjectureFor n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) →
    (∀ (n : ℕ) (hn : n > 3), ¬ FugledeConjectureFor n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) →
    (∀ (n : ℕ) (hn : n > 3), ¬ FugledeConjectureFor n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) →
    (∀ (n : ℕ) (hn : n > 3), ¬ FugledeConjectureFor n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (n > 3) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (n > 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (n > 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (n > 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (n > 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (n > 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (n > 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (n > 3))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (n > 3))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (n > 3))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (n > 3))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (n > 3))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (n > 3))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (n > 3))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n > 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n > 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n > 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n > 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n > 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n > 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n > 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 4), ¬ FugledeConjectureFor n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) →
    (∀ (n : ℕ) (hn : n ≥ 4), ¬ FugledeConjectureFor n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) →
    (∀ (n : ℕ) (hn : n ≥ 4), ¬ FugledeConjectureFor n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) →
    (∀ (n : ℕ) (hn : n ≥ 4), ¬ FugledeConjectureFor n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) →
    (∀ (n : ℕ) (hn : n ≥ 4), ¬ FugledeConjectureFor n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) →
    (∀ (n : ℕ) (hn : n ≥ 4), ¬ FugledeConjectureFor n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) →
    (∀ (n : ℕ) (hn : n ≥ 4), ¬ FugledeConjectureFor n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) →
    (∀ (n : ℕ) (hn : n ≥ 4), ¬ FugledeConjectureFor n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (n ≥ 4) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (n ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (n ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (n ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (n ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (n ≥ 4) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (n ≥ 4) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (n ≥ 4))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (n ≥ 4))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (n ≥ 4))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (n ≥ 4))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (n ≥ 4))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (n ≥ 4))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (n ≥ 4))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n ≥ 4)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n ≥ 4)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n ≥ 4)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n ≥ 4)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n ≥ 4)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n ≥ 4)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n ≥ 4)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), ¬ FugledeConjectureFor n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ¬ FugledeConjectureFor n) →
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ¬ FugledeConjectureFor n) →
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ¬ FugledeConjectureFor n) →
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ¬ FugledeConjectureFor n) →
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ¬ FugledeConjectureFor n) →
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ¬ FugledeConjectureFor n) →
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ¬ FugledeConjectureFor n) →
    (∀ (n : ℕ) (hn : 3 ≤ n), ¬ FugledeConjectureFor n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (2 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (2 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (2 ≤ n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (2 ≤ n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (2 ≤ n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (2 ≤ n))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (2 ≤ n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (2 ≤ n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (2 ≤ n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (2 ≤ n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (2 ≤ n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (2 ≤ n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (2 ≤ n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (2 ≤ n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (2 ≤ n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (2 ≤ n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (2 ≤ n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 3 ≤ n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 3 ≤ n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 3 ≤ n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 3 ≤ n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 3 ≤ n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
