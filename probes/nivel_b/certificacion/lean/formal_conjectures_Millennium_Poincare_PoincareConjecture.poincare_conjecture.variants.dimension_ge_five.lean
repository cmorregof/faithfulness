import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   notación `ℝ^n` (scoped EuclideanGeometry, FCM.Geometry.Euclidean)
/-! # The Poincaré Conjecture

References:
- [Miln2022](https://www.claymath.org/wp-content/uploads/2022/06/poincare.pdf)
- [Wang2017](https://annals.math.princeton.edu/2017/186-2/p03).
- [mo296171](https://mathoverflow.net/questions/296171/unique-smooth-structure-on-3-manifolds)
- [mathlib4](https://github.com/leanprover-community/mathlib4)

The formalisations in this file are based on the ones written by Junyan Xu in Mathlib4.
-/

section

universe u

namespace PoincareConjecture

open scoped Manifold ContDiff EuclideanGeometry ContinuousMap

local macro:max "𝕊" noWs n:superscript(term) : term =>
  `(Metric.sphere (0 : EuclideanSpace ℝ (Fin ($(⟨n.raw[0]⟩) + 1))) 1)

/-- The predicate that the generalized Poincaré conjecture holds in dimension $n$, i.e. that
any $n$-dimensional manifold that is homotopy equivalent to the sphere is in fact homeomorphic
to the sphere. -/
def ConjectureFor (n : ℕ) : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (ℝ^n) M], M ≃ₕ 𝕊ⁿ → Nonempty (M ≃ₜ 𝕊ⁿ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 5 < n), ConjectureFor n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n) →
    (∀ (n : ℕ) (hn : 5 < n), ConjectureFor n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n) →
    (∀ (n : ℕ) (hn : 5 < n), ConjectureFor n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n) →
    (∀ (n : ℕ) (hn : 5 < n), ConjectureFor n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n) →
    (∀ (n : ℕ) (hn : 5 < n), ConjectureFor n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n) →
    (∀ (n : ℕ) (hn : 5 < n), ConjectureFor n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n) →
    (∀ (n : ℕ) (hn : 5 < n), ConjectureFor n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n) →
    (∀ (n : ℕ) (hn : 5 < n), ConjectureFor n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (5 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (5 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (5 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (5 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (5 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (5 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (5 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (5 < n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (5 < n))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (5 < n))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (5 < n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (5 < n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (5 < n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (5 < n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (5 < n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (5 < n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (5 < n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (5 < n)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (5 < n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (5 < n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (5 < n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (5 < n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (5 < n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 6 ≤ n), ConjectureFor n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n) →
    (∀ (n : ℕ) (hn : 6 ≤ n), ConjectureFor n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n) →
    (∀ (n : ℕ) (hn : 6 ≤ n), ConjectureFor n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n) →
    (∀ (n : ℕ) (hn : 6 ≤ n), ConjectureFor n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n) →
    (∀ (n : ℕ) (hn : 6 ≤ n), ConjectureFor n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n) →
    (∀ (n : ℕ) (hn : 6 ≤ n), ConjectureFor n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n) →
    (∀ (n : ℕ) (hn : 6 ≤ n), ConjectureFor n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n) →
    (∀ (n : ℕ) (hn : 6 ≤ n), ConjectureFor n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (6 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (6 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (6 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (6 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (6 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (6 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (6 ≤ n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (6 ≤ n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (6 ≤ n))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (6 ≤ n))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (6 ≤ n))) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (6 ≤ n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (6 ≤ n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (6 ≤ n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (6 ≤ n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (6 ≤ n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (6 ≤ n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (6 ≤ n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (6 ≤ n)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (6 ≤ n)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (6 ≤ n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (6 ≤ n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (6 ≤ n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (6 ≤ n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (6 ≤ n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 5), ConjectureFor n

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (n ≥ 5) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (n ≥ 5) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (n ≥ 5) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (n ≥ 5) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (n ≥ 5) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (n ≥ 5) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (n ≥ 5) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (n ≥ 5) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n) ↔
    (∀ (n : ℕ) (hn : n ≥ 5), ConjectureFor n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n) ↔
    (∀ (n : ℕ) (hn : n ≥ 5), ConjectureFor n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n) ↔
    (∀ (n : ℕ) (hn : n ≥ 5), ConjectureFor n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n) ↔
    (∀ (n : ℕ) (hn : n ≥ 5), ConjectureFor n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn₀ : 5 ≤ n), ConjectureFor n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n) ↔
    (∀ (n : ℕ) (hn₀ : 5 ≤ n), ConjectureFor n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n) ↔
    (∀ (n : ℕ) (hn₀ : 5 ≤ n), ConjectureFor n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n) ↔
    (∀ (n : ℕ) (hn₀ : 5 ≤ n), ConjectureFor n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n) ↔
    (∀ (n : ℕ) (hn₀ : 5 ≤ n), ConjectureFor n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : ¬(n < 5)), ConjectureFor n

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (¬(n < 5)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (¬(n < 5)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (¬(n < 5)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (¬(n < 5)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (¬(n < 5)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (¬(n < 5)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (¬(n < 5)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (¬(n < 5)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n) ↔
    (∀ (n : ℕ) (hn : ¬(n < 5)), ConjectureFor n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n) ↔
    (∀ (n : ℕ) (hn : ¬(n < 5)), ConjectureFor n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n) ↔
    (∀ (n : ℕ) (hn : ¬(n < 5)), ConjectureFor n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n) ↔
    (∀ (n : ℕ) (hn : ¬(n < 5)), ConjectureFor n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 4 < n), ConjectureFor n

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (4 < n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (4 < n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (4 < n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (4 < n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (4 < n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (4 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (4 < n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (5 ≤ n) ↔ (4 < n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n) ↔
    (∀ (n : ℕ) (hn : 4 < n), ConjectureFor n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n) ↔
    (∀ (n : ℕ) (hn : 4 < n), ConjectureFor n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n) ↔
    (∀ (n : ℕ) (hn : 4 < n), ConjectureFor n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n) ↔
    (∀ (n : ℕ) (hn : 4 < n), ConjectureFor n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 5), ConjectureFor n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n) →
    (∀ (n : ℕ) (hn : n > 5), ConjectureFor n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n) →
    (∀ (n : ℕ) (hn : n > 5), ConjectureFor n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n) →
    (∀ (n : ℕ) (hn : n > 5), ConjectureFor n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n) →
    (∀ (n : ℕ) (hn : n > 5), ConjectureFor n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n) →
    (∀ (n : ℕ) (hn : n > 5), ConjectureFor n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n) →
    (∀ (n : ℕ) (hn : n > 5), ConjectureFor n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n) →
    (∀ (n : ℕ) (hn : n > 5), ConjectureFor n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (n > 5) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (n > 5) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (n > 5) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (n > 5) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (n > 5) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (n > 5) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (n > 5) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (n > 5))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (n > 5))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (n > 5))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (n > 5))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (n > 5))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (n > 5))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (n > 5))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (n > 5))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (n > 5)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (n > 5)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (n > 5)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (n > 5)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (n > 5)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (n > 5)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (n > 5)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (n > 5)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 6), ConjectureFor n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n) →
    (∀ (n : ℕ) (hn : n ≥ 6), ConjectureFor n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n) →
    (∀ (n : ℕ) (hn : n ≥ 6), ConjectureFor n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n) →
    (∀ (n : ℕ) (hn : n ≥ 6), ConjectureFor n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n) →
    (∀ (n : ℕ) (hn : n ≥ 6), ConjectureFor n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n) →
    (∀ (n : ℕ) (hn : n ≥ 6), ConjectureFor n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n) →
    (∀ (n : ℕ) (hn : n ≥ 6), ConjectureFor n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ≤ n), ConjectureFor n) →
    (∀ (n : ℕ) (hn : n ≥ 6), ConjectureFor n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (n ≥ 6) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (n ≥ 6) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (n ≥ 6) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (n ≥ 6) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (n ≥ 6) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (n ≥ 6) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (5 ≤ n) ↔ (n ≥ 6) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (n ≥ 6))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (n ≥ 6))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (n ≥ 6))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (n ≥ 6))) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (n ≥ 6))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (n ≥ 6))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (n ≥ 6))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (n ≥ 6))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((5 ≤ n) ↔ (n ≥ 6))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (n ≥ 6)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (n ≥ 6)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (n ≥ 6)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (n ≥ 6)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (n ≥ 6)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (n ≥ 6)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (n ≥ 6)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (n ≥ 6)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((5 ≤ n) ↔ (n ≥ 6)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 5 ≤ n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 5 ≤ n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 5 ≤ n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 5 ≤ n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 5 ≤ n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
