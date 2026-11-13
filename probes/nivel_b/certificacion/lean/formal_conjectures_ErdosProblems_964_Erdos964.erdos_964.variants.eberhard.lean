import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 964

*References:*
- [erdosproblems.com/964](https://www.erdosproblems.com/964)
- [Er86b] Erdős, P., *Some problems on number theory*. Proceedings of the seventeenth Southeastern
  international conference on combinatorics, graph theory, and computing (Boca Raton, Fla.,
  1986), Congr. Numer. 54 (1986), 225-244.
- [Eb25] Eberhard, S., *Ratios of consecutive values of the divisor function*.
  [arXiv:2505.00727](https://arxiv.org/abs/2505.00727) (2025).
-/

section

open scoped ArithmeticFunction.sigma

namespace Erdos964

/-- $\tau(n+1)/\tau(n)$ as a real number, where $\tau = \sigma_0$ counts divisors. For $n = 0$
this is the junk value $0$, so the statements below use $n \geq 1$. -/
noncomputable def tauRatio (n : ℕ) : ℝ := (σ 0 (n + 1) : ℝ) / (σ 0 n : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℚ) (hq : 0 < q), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℚ) (hq : 0 ≤ q), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℚ) (hq : 0 ≤ q), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) →
    (∀ (q : ℚ) (hq : 0 < q), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℚ) (hq : 0 ≤ q), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) →
    (∀ (q : ℚ) (hq : 0 < q), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℚ) (hq : 0 ≤ q), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) →
    (∀ (q : ℚ) (hq : 0 < q), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℚ) (hq : 0 ≤ q), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) →
    (∀ (q : ℚ) (hq : 0 < q), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℚ) (hq : 0 ≤ q), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) →
    (∀ (q : ℚ) (hq : 0 < q), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℚ) (hq : 0 ≤ q), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) →
    (∀ (q : ℚ) (hq : 0 < q), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℚ) (hq : 0 ≤ q), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) →
    (∀ (q : ℚ) (hq : 0 < q), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (q : ℚ)  :
    (0 < q) ↔ (0 ≤ q) := by
  omega

set_option maxHeartbeats 200000 in
example (q : ℚ)  :
    (0 < q) ↔ (0 ≤ q) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (q : ℚ)  :
    (0 < q) ↔ (0 ≤ q) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (q : ℚ)  :
    (0 < q) ↔ (0 ≤ q) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (q : ℚ)  :
    (0 < q) ↔ (0 ≤ q) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (q : ℚ)  :
    (0 < q) ↔ (0 ≤ q) := by
  simp_all

set_option maxHeartbeats 200000 in
example (q : ℚ)  :
    (0 < q) ↔ (0 ≤ q) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (q : ℚ), (¬((0 < q) ↔ (0 ≤ q))) :=
  ⟨(0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℚ), (¬((0 < q) ↔ (0 ≤ q))) :=
  ⟨(-1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℚ), (¬((0 < q) ↔ (0 ≤ q))) :=
  ⟨(1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℚ), (¬((0 < q) ↔ (0 ≤ q))) :=
  ⟨(2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℚ), (¬((0 < q) ↔ (0 ≤ q))) :=
  ⟨(1/2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℚ), (¬((0 < q) ↔ (0 ≤ q))) :=
  ⟨(3 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℚ), ¬((0 < q) ↔ (0 ≤ q)) :=
  ⟨(0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℚ), ¬((0 < q) ↔ (0 ≤ q)) :=
  ⟨(-1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℚ), ¬((0 < q) ↔ (0 ≤ q)) :=
  ⟨(1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℚ), ¬((0 < q) ↔ (0 ≤ q)) :=
  ⟨(2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℚ), ¬((0 < q) ↔ (0 ≤ q)) :=
  ⟨(1/2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℚ), ¬((0 < q) ↔ (0 ≤ q)) :=
  ⟨(3 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℚ) (hq : 0 < q), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℚ) (hq : q > 0), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite

set_option maxHeartbeats 200000 in
example (q : ℚ) :
    (0 < q) ↔ (q > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (q : ℚ) :
    (0 < q) ↔ (q > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (q : ℚ) :
    (0 < q) ↔ (q > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (q : ℚ) :
    (0 < q) ↔ (q > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (q : ℚ) :
    (0 < q) ↔ (q > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (q : ℚ) :
    (0 < q) ↔ (q > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (q : ℚ) :
    (0 < q) ↔ (q > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (q : ℚ) :
    (0 < q) ↔ (q > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℚ) (hq : 0 < q), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) ↔
    (∀ (q : ℚ) (hq : q > 0), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℚ) (hq : 0 < q), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) ↔
    (∀ (q : ℚ) (hq : q > 0), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℚ) (hq : 0 < q), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) ↔
    (∀ (q : ℚ) (hq : q > 0), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℚ) (hq : 0 < q), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) ↔
    (∀ (q : ℚ) (hq : q > 0), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℚ) (hq : 0 < q), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℚ) (hq₀ : 0 < q), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℚ) (hq : 0 < q), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) ↔
    (∀ (q : ℚ) (hq₀ : 0 < q), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℚ) (hq : 0 < q), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) ↔
    (∀ (q : ℚ) (hq₀ : 0 < q), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℚ) (hq : 0 < q), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) ↔
    (∀ (q : ℚ) (hq₀ : 0 < q), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℚ) (hq : 0 < q), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) ↔
    (∀ (q : ℚ) (hq₀ : 0 < q), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℚ) (hq : 0 < q), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℚ) (hq : ¬(q ≤ 0)), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite

set_option maxHeartbeats 200000 in
example (q : ℚ) :
    (0 < q) ↔ (¬(q ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (q : ℚ) :
    (0 < q) ↔ (¬(q ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (q : ℚ) :
    (0 < q) ↔ (¬(q ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (q : ℚ) :
    (0 < q) ↔ (¬(q ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (q : ℚ) :
    (0 < q) ↔ (¬(q ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (q : ℚ) :
    (0 < q) ↔ (¬(q ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (q : ℚ) :
    (0 < q) ↔ (¬(q ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (q : ℚ) :
    (0 < q) ↔ (¬(q ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℚ) (hq : 0 < q), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) ↔
    (∀ (q : ℚ) (hq : ¬(q ≤ 0)), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℚ) (hq : 0 < q), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) ↔
    (∀ (q : ℚ) (hq : ¬(q ≤ 0)), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℚ) (hq : 0 < q), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) ↔
    (∀ (q : ℚ) (hq : ¬(q ≤ 0)), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℚ) (hq : 0 < q), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) ↔
    (∀ (q : ℚ) (hq : ¬(q ≤ 0)), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℚ) (hq : 0 < q), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℚ) (hq : q ≥ 0), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℚ) (hq : q ≥ 0), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) →
    (∀ (q : ℚ) (hq : 0 < q), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℚ) (hq : q ≥ 0), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) →
    (∀ (q : ℚ) (hq : 0 < q), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℚ) (hq : q ≥ 0), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) →
    (∀ (q : ℚ) (hq : 0 < q), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℚ) (hq : q ≥ 0), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) →
    (∀ (q : ℚ) (hq : 0 < q), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℚ) (hq : q ≥ 0), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) →
    (∀ (q : ℚ) (hq : 0 < q), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℚ) (hq : q ≥ 0), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) →
    (∀ (q : ℚ) (hq : 0 < q), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℚ) (hq : q ≥ 0), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) →
    (∀ (q : ℚ) (hq : 0 < q), {n : ℕ | 0 < n ∧ tauRatio n = q}.Infinite) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (q : ℚ)  :
    (0 < q) ↔ (q ≥ 0) := by
  omega

set_option maxHeartbeats 200000 in
example (q : ℚ)  :
    (0 < q) ↔ (q ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (q : ℚ)  :
    (0 < q) ↔ (q ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (q : ℚ)  :
    (0 < q) ↔ (q ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (q : ℚ)  :
    (0 < q) ↔ (q ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (q : ℚ)  :
    (0 < q) ↔ (q ≥ 0) := by
  simp_all

set_option maxHeartbeats 200000 in
example (q : ℚ)  :
    (0 < q) ↔ (q ≥ 0) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (q : ℚ), (¬((0 < q) ↔ (q ≥ 0))) :=
  ⟨(0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℚ), (¬((0 < q) ↔ (q ≥ 0))) :=
  ⟨(-1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℚ), (¬((0 < q) ↔ (q ≥ 0))) :=
  ⟨(1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℚ), (¬((0 < q) ↔ (q ≥ 0))) :=
  ⟨(2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℚ), (¬((0 < q) ↔ (q ≥ 0))) :=
  ⟨(1/2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℚ), (¬((0 < q) ↔ (q ≥ 0))) :=
  ⟨(3 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℚ), ¬((0 < q) ↔ (q ≥ 0)) :=
  ⟨(0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℚ), ¬((0 < q) ↔ (q ≥ 0)) :=
  ⟨(-1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℚ), ¬((0 < q) ↔ (q ≥ 0)) :=
  ⟨(1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℚ), ¬((0 < q) ↔ (q ≥ 0)) :=
  ⟨(2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℚ), ¬((0 < q) ↔ (q ≥ 0)) :=
  ⟨(1/2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℚ), ¬((0 < q) ↔ (q ≥ 0)) :=
  ⟨(3 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (q : ℚ) (hq : 0 < q) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (q : ℚ) (hq : 0 < q) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (q : ℚ) (hq : 0 < q) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (q : ℚ) (hq : 0 < q) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (q : ℚ) (hq : 0 < q) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
