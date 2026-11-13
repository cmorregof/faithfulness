import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   notación `ℝ²` (scoped EuclideanGeometry, FCM.Geometry.2d)
/-!
# Gauss circle problem

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Gauss_circle_problem)
-/

section

open Filter

open scoped EuclideanGeometry Real Topology

/-  # Gauss Circle Problem

Consider a circle in $\mathbb{R}^2$ with center at the origin and radius $r\geq 0$.
Gauss's circle problem asks how many points there are inside this circle of the form
$(m, n)$ where $m$ and $n$ are both integers. Equivalently, how many pairs of integers
$m$ and $n$ are there such that
$$
  m^2 + n^2 \leq r^2.
$$
-/

namespace GaussCircleProblem

/--
Let $N(r)$ be the number of points $(m, n)$ within a circle of radius $r$,
where $m$ and $n$ are both integers.
-/
noncomputable abbrev N (r : ℝ) : ℕ :=
  { (m, n) : ℤ × ℤ | !₂[↑m, ↑n] ∈ Metric.closedBall (0 : ℝ²) r }.ncard

/--
Let $E(r)$ be the error term between the number of integral points inside the circle and the
area of the circle; that is $N(r) = \pi r^2 + E(r)$.
-/
noncomputable abbrev E (r : ℝ) : ℝ := N r - π * r ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℝ) (hr : 0 < r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) →
    (∀ (r : ℝ) (hr : 0 < r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) →
    (∀ (r : ℝ) (hr : 0 < r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) →
    (∀ (r : ℝ) (hr : 0 < r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) →
    (∀ (r : ℝ) (hr : 0 < r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) →
    (∀ (r : ℝ) (hr : 0 < r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) →
    (∀ (r : ℝ) (hr : 0 < r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) →
    (∀ (r : ℝ) (hr : 0 < r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (r : ℝ)  :
    (0 ≤ r) ↔ (0 < r) := by
  omega

set_option maxHeartbeats 200000 in
example (r : ℝ)  :
    (0 ≤ r) ↔ (0 < r) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (r : ℝ)  :
    (0 ≤ r) ↔ (0 < r) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (r : ℝ)  :
    (0 ≤ r) ↔ (0 < r) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (r : ℝ)  :
    (0 ≤ r) ↔ (0 < r) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (r : ℝ)  :
    (0 ≤ r) ↔ (0 < r) := by
  simp_all

set_option maxHeartbeats 200000 in
example (r : ℝ)  :
    (0 ≤ r) ↔ (0 < r) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), (¬((0 ≤ r) ↔ (0 < r))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), (¬((0 ≤ r) ↔ (0 < r))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), (¬((0 ≤ r) ↔ (0 < r))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), (¬((0 ≤ r) ↔ (0 < r))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), (¬((0 ≤ r) ↔ (0 < r))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), (¬((0 ≤ r) ↔ (0 < r))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((0 ≤ r) ↔ (0 < r)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((0 ≤ r) ↔ (0 < r)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((0 ≤ r) ↔ (0 < r)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((0 ≤ r) ↔ (0 < r)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((0 ≤ r) ↔ (0 < r)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((0 ≤ r) ↔ (0 < r)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) →
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) →
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) →
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) →
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) →
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) →
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) →
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) →
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) →
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) →
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) →
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) →
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) →
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) →
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), (0 ≤ r) ∧ (¬(N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), (0 ≤ r) ∧ (¬(N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), (0 ≤ r) ∧ (¬(N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), (0 ≤ r) ∧ (¬(N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), (0 ≤ r) ∧ (¬(N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋))) :=
  ⟨(5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), (0 ≤ r) ∧ (¬(N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋))) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), (0 ≤ r) ∧ (¬(N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋))) :=
  ⟨(6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), (0 ≤ r) ∧ (¬(N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), (0 ≤ r) ∧ (¬(N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) ↔ (N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) ↔ (N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) ↔ (N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) ↔ (N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋))) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) ↔ (N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) ↔ (N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋))) :=
  ⟨(5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) ↔ (N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋))) :=
  ⟨(6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) ↔ (N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) ↔ (N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℝ) (hr : r ≥ 0), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)

set_option maxHeartbeats 200000 in
example (r : ℝ) :
    (0 ≤ r) ↔ (r ≥ 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (r : ℝ) :
    (0 ≤ r) ↔ (r ≥ 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (r : ℝ) :
    (0 ≤ r) ↔ (r ≥ 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (r : ℝ) :
    (0 ≤ r) ↔ (r ≥ 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (r : ℝ) :
    (0 ≤ r) ↔ (r ≥ 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (r : ℝ) :
    (0 ≤ r) ↔ (r ≥ 0) := by
  omega

set_option maxHeartbeats 200000 in
example (r : ℝ) :
    (0 ≤ r) ↔ (r ≥ 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (r : ℝ) :
    (0 ≤ r) ↔ (r ≥ 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) ↔
    (∀ (r : ℝ) (hr : r ≥ 0), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) ↔
    (∀ (r : ℝ) (hr : r ≥ 0), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) ↔
    (∀ (r : ℝ) (hr : r ≥ 0), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) ↔
    (∀ (r : ℝ) (hr : r ≥ 0), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℝ) (hr₀ : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) ↔
    (∀ (r : ℝ) (hr₀ : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) ↔
    (∀ (r : ℝ) (hr₀ : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) ↔
    (∀ (r : ℝ) (hr₀ : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) ↔
    (∀ (r : ℝ) (hr₀ : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℝ) (hr : ¬(r < 0)), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)

set_option maxHeartbeats 200000 in
example (r : ℝ) :
    (0 ≤ r) ↔ (¬(r < 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (r : ℝ) :
    (0 ≤ r) ↔ (¬(r < 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (r : ℝ) :
    (0 ≤ r) ↔ (¬(r < 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (r : ℝ) :
    (0 ≤ r) ↔ (¬(r < 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (r : ℝ) :
    (0 ≤ r) ↔ (¬(r < 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (r : ℝ) :
    (0 ≤ r) ↔ (¬(r < 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (r : ℝ) :
    (0 ≤ r) ↔ (¬(r < 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (r : ℝ) :
    (0 ≤ r) ↔ (¬(r < 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) ↔
    (∀ (r : ℝ) (hr : ¬(r < 0)), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) ↔
    (∀ (r : ℝ) (hr : ¬(r < 0)), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) ↔
    (∀ (r : ℝ) (hr : ¬(r < 0)), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) ↔
    (∀ (r : ℝ) (hr : ¬(r < 0)), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℝ) (hr : r > 0), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) →
    (∀ (r : ℝ) (hr : r > 0), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) →
    (∀ (r : ℝ) (hr : r > 0), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) →
    (∀ (r : ℝ) (hr : r > 0), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) →
    (∀ (r : ℝ) (hr : r > 0), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) →
    (∀ (r : ℝ) (hr : r > 0), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) →
    (∀ (r : ℝ) (hr : r > 0), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) →
    (∀ (r : ℝ) (hr : r > 0), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (r : ℝ)  :
    (0 ≤ r) ↔ (r > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (r : ℝ)  :
    (0 ≤ r) ↔ (r > 0) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (r : ℝ)  :
    (0 ≤ r) ↔ (r > 0) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (r : ℝ)  :
    (0 ≤ r) ↔ (r > 0) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (r : ℝ)  :
    (0 ≤ r) ↔ (r > 0) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (r : ℝ)  :
    (0 ≤ r) ↔ (r > 0) := by
  simp_all

set_option maxHeartbeats 200000 in
example (r : ℝ)  :
    (0 ≤ r) ↔ (r > 0) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), (¬((0 ≤ r) ↔ (r > 0))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), (¬((0 ≤ r) ↔ (r > 0))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), (¬((0 ≤ r) ↔ (r > 0))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), (¬((0 ≤ r) ↔ (r > 0))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), (¬((0 ≤ r) ↔ (r > 0))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), (¬((0 ≤ r) ↔ (r > 0))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((0 ≤ r) ↔ (r > 0)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((0 ≤ r) ↔ (r > 0)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((0 ≤ r) ↔ (r > 0)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((0 ≤ r) ↔ (r > 0)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((0 ≤ r) ↔ (r > 0)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((0 ≤ r) ↔ (r > 0)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℝ) (hr : r ≥ 0), N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r ≥ 0), N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) →
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r ≥ 0), N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) →
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r ≥ 0), N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) →
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r ≥ 0), N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) →
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r ≥ 0), N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) →
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r ≥ 0), N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) →
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : r ≥ 0), N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) →
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) →
    (∀ (r : ℝ) (hr : r ≥ 0), N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) →
    (∀ (r : ℝ) (hr : r ≥ 0), N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) →
    (∀ (r : ℝ) (hr : r ≥ 0), N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) →
    (∀ (r : ℝ) (hr : r ≥ 0), N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) →
    (∀ (r : ℝ) (hr : r ≥ 0), N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) →
    (∀ (r : ℝ) (hr : r ≥ 0), N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℝ) (hr : 0 ≤ r), N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) →
    (∀ (r : ℝ) (hr : r ≥ 0), N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), (0 ≤ r) ∧ (¬(N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), (0 ≤ r) ∧ (¬(N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), (0 ≤ r) ∧ (¬(N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), (0 ≤ r) ∧ (¬(N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), (0 ≤ r) ∧ (¬(N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋))) :=
  ⟨(5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), (0 ≤ r) ∧ (¬(N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋))) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), (0 ≤ r) ∧ (¬(N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋))) :=
  ⟨(6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), (0 ≤ r) ∧ (¬(N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), (0 ≤ r) ∧ (¬(N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) ↔ (N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) ↔ (N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) ↔ (N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) ↔ (N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋))) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) ↔ (N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) ↔ (N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋))) :=
  ⟨(5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) ↔ (N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋))) :=
  ⟨(6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) ↔ (N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℝ), ¬((N r = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)) ↔ (N r = 1 + 5 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (r : ℝ) (hr : 0 ≤ r) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (r : ℝ) (hr : 0 ≤ r) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (r : ℝ) (hr : 0 ≤ r) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (r : ℝ) (hr : 0 ≤ r) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (r : ℝ) (hr : 0 ≤ r) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
