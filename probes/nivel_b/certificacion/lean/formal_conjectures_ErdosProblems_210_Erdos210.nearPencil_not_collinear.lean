import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Geometry.OrdinaryLines
--   import FormalConjecturesForMathlib.Geometry.2d
--   notación `ℝ²` (scoped EuclideanGeometry, FCM.Geometry.2d)
/-!
# Erdős Problem 210

*References:*
- [erdosproblems.com/210](https://www.erdosproblems.com/210)
- [Mo51] Motzkin, T. S., *The lines and planes connecting the points of a finite set*.
  Transactions of the American Mathematical Society 70 (1951), 451–464.
- [KeMo58] Kelly, L. M. and Moser, W. O. J., *On the number of ordinary lines determined by
  n points*. Canadian Journal of Mathematics 10 (1958), 210–219.
- [CsSa93] Csima, J. and Sawyer, E. T., *There exist 6n/13 ordinary points*.
  Discrete & Computational Geometry 9 (1993), 187–202.
- [GrTa13] Green, B. and Tao, T., *On sets defining few ordinary lines*.
  Discrete & Computational Geometry 50 (2013), 409–468.
-/

section

namespace Erdos210

open EuclideanGeometry Filter

/-- The sharp ordinary-line guarantee for noncollinear sets of $n$ points.
For $n<3$, there are no such configurations, and the infimum is $0$. -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ s : Finset ℝ²,
    s.card = n ∧ ¬ Collinear ℝ (s : Set ℝ²) ∧ (ordinaryLines s).card = m}

/-- Points used for a configuration with all but one point on a single line. -/
def axisPoint (i : ℕ) : ℝ² := !₂[(i : ℝ), 0]

/-- The point off that line. -/
def apex : ℝ² := !₂[(0 : ℝ), 1]

/-- The near-pencil configuration consists of $n-1$ points on the horizontal axis and an apex. -/
noncomputable def nearPencil (n : ℕ) : Finset ℝ² := by
  classical
  exact insert apex ((Finset.range (n - 1)).image axisPoint)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 3 < n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) →
    (∀ {n : ℕ} (hn : 3 < n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) →
    (∀ {n : ℕ} (hn : 3 < n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) →
    (∀ {n : ℕ} (hn : 3 < n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) →
    (∀ {n : ℕ} (hn : 3 < n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) →
    (∀ {n : ℕ} (hn : 3 < n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) →
    (∀ {n : ℕ} (hn : 3 < n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) →
    (∀ {n : ℕ} (hn : 3 < n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (3 < n) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (3 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (3 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (3 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (3 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (3 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
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
  ∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 4 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) →
    (∀ {n : ℕ} (hn : 4 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) →
    (∀ {n : ℕ} (hn : 4 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) →
    (∀ {n : ℕ} (hn : 4 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) →
    (∀ {n : ℕ} (hn : 4 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) →
    (∀ {n : ℕ} (hn : 4 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) →
    (∀ {n : ℕ} (hn : 4 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) →
    (∀ {n : ℕ} (hn : 4 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (4 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (4 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (4 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (4 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (4 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (4 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
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
  ∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : n ≥ 3), ¬ Collinear ℝ (nearPencil n : Set ℝ²)

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (n ≥ 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (n ≥ 3) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (n ≥ 3) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (n ≥ 3) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (n ≥ 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (n ≥ 3) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (n ≥ 3) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (n ≥ 3) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) ↔
    (∀ {n : ℕ} (hn : n ≥ 3), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) ↔
    (∀ {n : ℕ} (hn : n ≥ 3), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) ↔
    (∀ {n : ℕ} (hn : n ≥ 3), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) ↔
    (∀ {n : ℕ} (hn : n ≥ 3), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn₀ : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) ↔
    (∀ {n : ℕ} (hn₀ : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) ↔
    (∀ {n : ℕ} (hn₀ : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) ↔
    (∀ {n : ℕ} (hn₀ : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) ↔
    (∀ {n : ℕ} (hn₀ : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : ¬(n < 3)), ¬ Collinear ℝ (nearPencil n : Set ℝ²)

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) ↔
    (∀ {n : ℕ} (hn : ¬(n < 3)), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) ↔
    (∀ {n : ℕ} (hn : ¬(n < 3)), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) ↔
    (∀ {n : ℕ} (hn : ¬(n < 3)), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) ↔
    (∀ {n : ℕ} (hn : ¬(n < 3)), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 2 < n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (2 < n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (2 < n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (2 < n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (2 < n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (2 < n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (2 < n) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) ↔
    (∀ {n : ℕ} (hn : 2 < n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) ↔
    (∀ {n : ℕ} (hn : 2 < n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) ↔
    (∀ {n : ℕ} (hn : 2 < n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) ↔
    (∀ {n : ℕ} (hn : 2 < n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : n > 3), ¬ Collinear ℝ (nearPencil n : Set ℝ²)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) →
    (∀ {n : ℕ} (hn : n > 3), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) →
    (∀ {n : ℕ} (hn : n > 3), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) →
    (∀ {n : ℕ} (hn : n > 3), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) →
    (∀ {n : ℕ} (hn : n > 3), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) →
    (∀ {n : ℕ} (hn : n > 3), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) →
    (∀ {n : ℕ} (hn : n > 3), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) →
    (∀ {n : ℕ} (hn : n > 3), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (n > 3) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (n > 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (n > 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (n > 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (n > 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (n > 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
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
  ∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : n ≥ 4), ¬ Collinear ℝ (nearPencil n : Set ℝ²)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) →
    (∀ {n : ℕ} (hn : n ≥ 4), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) →
    (∀ {n : ℕ} (hn : n ≥ 4), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) →
    (∀ {n : ℕ} (hn : n ≥ 4), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) →
    (∀ {n : ℕ} (hn : n ≥ 4), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) →
    (∀ {n : ℕ} (hn : n ≥ 4), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) →
    (∀ {n : ℕ} (hn : n ≥ 4), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) →
    (∀ {n : ℕ} (hn : n ≥ 4), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (n ≥ 4) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (n ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (n ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (n ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (n ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (n ≥ 4) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
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
  ∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 2 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) →
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) →
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) →
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) →
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) →
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) →
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) →
    (∀ {n : ℕ} (hn : 3 ≤ n), ¬ Collinear ℝ (nearPencil n : Set ℝ²)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (2 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (2 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
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
example {n : ℕ} (hn : 3 ≤ n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 3 ≤ n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 3 ≤ n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 3 ≤ n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 3 ≤ n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
