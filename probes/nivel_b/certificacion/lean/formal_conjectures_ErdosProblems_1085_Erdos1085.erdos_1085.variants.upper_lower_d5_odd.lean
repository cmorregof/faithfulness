import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Geometry.Metric
--   notación `ℝ^n` (scoped EuclideanGeometry, FCM.Geometry.Euclidean)
/-!
# Erdős Problem 1085

Let f_d(n) be minimal such that, in any set of n points in ℝ^d, there exist at most f_d(n) pairs
of points which are distance 1 apart. Estimate f_d(n).

*Reference:* [erdosproblems.com/1085](https://www.erdosproblems.com/1085)
-/

section

open Filter Real
open scoped EuclideanGeometry Topology

namespace Erdos1085
variable {d : ℕ}

/-- The maximal number of pairs of points which are distance 1 apart that a set of `n` points in
`ℝ^d` make. -/
noncomputable def f (d n : ℕ) : ℕ := ⨆ (s : Finset (ℝ^ d)) (_ : s.card = n), unitDistNum s

-- TODO: Add erdos_1085.

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hd : 5 < d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) →
    (∀ (hd : 5 < d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) →
    (∀ (hd : 5 < d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) →
    (∀ (hd : 5 < d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) →
    (∀ (hd : 5 < d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) →
    (∀ (hd : 5 < d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) →
    (∀ (hd : 5 < d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) →
    (∀ (hd : 5 < d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example  (hd_odd : Odd d) :
    (5 ≤ d) ↔ (5 < d) := by
  omega

set_option maxHeartbeats 200000 in
example  (hd_odd : Odd d) :
    (5 ≤ d) ↔ (5 < d) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example  (hd_odd : Odd d) :
    (5 ≤ d) ↔ (5 < d) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example  (hd_odd : Odd d) :
    (5 ≤ d) ↔ (5 < d) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example  (hd_odd : Odd d) :
    (5 ≤ d) ↔ (5 < d) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example  (hd_odd : Odd d) :
    (5 ≤ d) ↔ (5 < d) := by
  simp_all

set_option maxHeartbeats 200000 in
example  (hd_odd : Odd d) :
    (5 ≤ d) ↔ (5 < d) := by
  plausible

set_option maxHeartbeats 200000 in
example : (Odd d) ∧ (¬((5 ≤ d) ↔ (5 < d))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (Odd d) ∧ (¬((5 ≤ d) ↔ (5 < d))) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((5 ≤ d) ↔ (5 < d)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((5 ≤ d) ↔ (5 < d)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hd : 6 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) →
    (∀ (hd : 6 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) →
    (∀ (hd : 6 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) →
    (∀ (hd : 6 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) →
    (∀ (hd : 6 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) →
    (∀ (hd : 6 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) →
    (∀ (hd : 6 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) →
    (∀ (hd : 6 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example  (hd_odd : Odd d) :
    (5 ≤ d) ↔ (6 ≤ d) := by
  omega

set_option maxHeartbeats 200000 in
example  (hd_odd : Odd d) :
    (5 ≤ d) ↔ (6 ≤ d) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example  (hd_odd : Odd d) :
    (5 ≤ d) ↔ (6 ≤ d) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example  (hd_odd : Odd d) :
    (5 ≤ d) ↔ (6 ≤ d) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example  (hd_odd : Odd d) :
    (5 ≤ d) ↔ (6 ≤ d) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example  (hd_odd : Odd d) :
    (5 ≤ d) ↔ (6 ≤ d) := by
  simp_all

set_option maxHeartbeats 200000 in
example  (hd_odd : Odd d) :
    (5 ≤ d) ↔ (6 ≤ d) := by
  plausible

set_option maxHeartbeats 200000 in
example : (Odd d) ∧ (¬((5 ≤ d) ↔ (6 ≤ d))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (Odd d) ∧ (¬((5 ≤ d) ↔ (6 ≤ d))) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((5 ≤ d) ↔ (6 ≤ d)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((5 ≤ d) ↔ (6 ≤ d)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hd : d ≥ 5) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)

set_option maxHeartbeats 200000 in
example  :
    (5 ≤ d) ↔ (d ≥ 5) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example  :
    (5 ≤ d) ↔ (d ≥ 5) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example  :
    (5 ≤ d) ↔ (d ≥ 5) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example  :
    (5 ≤ d) ↔ (d ≥ 5) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example  :
    (5 ≤ d) ↔ (d ≥ 5) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example  :
    (5 ≤ d) ↔ (d ≥ 5) := by
  omega

set_option maxHeartbeats 200000 in
example  :
    (5 ≤ d) ↔ (d ≥ 5) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example  :
    (5 ≤ d) ↔ (d ≥ 5) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) ↔
    (∀ (hd : d ≥ 5) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) ↔
    (∀ (hd : d ≥ 5) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) ↔
    (∀ (hd : d ≥ 5) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) ↔
    (∀ (hd : d ≥ 5) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)

set_option maxHeartbeats 200000 in
example  :
    (∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) ↔ (∃ c₁₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example  :
    (∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) ↔ (∃ c₁₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example  :
    (∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) ↔ (∃ c₁₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example  :
    (∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) ↔ (∃ c₁₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example  :
    (∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) ↔ (∃ c₁₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example  :
    (∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) ↔ (∃ c₁₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  omega

set_option maxHeartbeats 200000 in
example  :
    (∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) ↔ (∃ c₁₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example  :
    (∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) ↔ (∃ c₁₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) ↔
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) ↔
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) ↔
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) ↔
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hd_odd : Odd d) (hd : 5 ≤ d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) ↔
    (∀ (hd_odd : Odd d) (hd : 5 ≤ d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) ↔
    (∀ (hd_odd : Odd d) (hd : 5 ≤ d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) ↔
    (∀ (hd_odd : Odd d) (hd : 5 ≤ d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) ↔
    (∀ (hd_odd : Odd d) (hd : 5 ≤ d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hd₀ : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) ↔
    (∀ (hd₀ : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) ↔
    (∀ (hd₀ : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) ↔
    (∀ (hd₀ : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) ↔
    (∀ (hd₀ : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hd : ¬(d < 5)) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)

set_option maxHeartbeats 200000 in
example  :
    (5 ≤ d) ↔ (¬(d < 5)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example  :
    (5 ≤ d) ↔ (¬(d < 5)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example  :
    (5 ≤ d) ↔ (¬(d < 5)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example  :
    (5 ≤ d) ↔ (¬(d < 5)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example  :
    (5 ≤ d) ↔ (¬(d < 5)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example  :
    (5 ≤ d) ↔ (¬(d < 5)) := by
  omega

set_option maxHeartbeats 200000 in
example  :
    (5 ≤ d) ↔ (¬(d < 5)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example  :
    (5 ≤ d) ↔ (¬(d < 5)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) ↔
    (∀ (hd : ¬(d < 5)) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) ↔
    (∀ (hd : ¬(d < 5)) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) ↔
    (∀ (hd : ¬(d < 5)) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) ↔
    (∀ (hd : ¬(d < 5)) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hd : d > 5) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) →
    (∀ (hd : d > 5) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) →
    (∀ (hd : d > 5) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) →
    (∀ (hd : d > 5) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) →
    (∀ (hd : d > 5) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) →
    (∀ (hd : d > 5) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) →
    (∀ (hd : d > 5) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) →
    (∀ (hd : d > 5) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example  (hd_odd : Odd d) :
    (5 ≤ d) ↔ (d > 5) := by
  omega

set_option maxHeartbeats 200000 in
example  (hd_odd : Odd d) :
    (5 ≤ d) ↔ (d > 5) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example  (hd_odd : Odd d) :
    (5 ≤ d) ↔ (d > 5) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example  (hd_odd : Odd d) :
    (5 ≤ d) ↔ (d > 5) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example  (hd_odd : Odd d) :
    (5 ≤ d) ↔ (d > 5) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example  (hd_odd : Odd d) :
    (5 ≤ d) ↔ (d > 5) := by
  simp_all

set_option maxHeartbeats 200000 in
example  (hd_odd : Odd d) :
    (5 ≤ d) ↔ (d > 5) := by
  plausible

set_option maxHeartbeats 200000 in
example : (Odd d) ∧ (¬((5 ≤ d) ↔ (d > 5))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (Odd d) ∧ (¬((5 ≤ d) ↔ (d > 5))) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((5 ≤ d) ↔ (d > 5)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((5 ≤ d) ↔ (d > 5)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hd : d ≥ 6) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) →
    (∀ (hd : d ≥ 6) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) →
    (∀ (hd : d ≥ 6) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) →
    (∀ (hd : d ≥ 6) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) →
    (∀ (hd : d ≥ 6) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) →
    (∀ (hd : d ≥ 6) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) →
    (∀ (hd : d ≥ 6) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (hd : 5 ≤ d) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) →
    (∀ (hd : d ≥ 6) (hd_odd : Odd d), ∃ c₁ > (0 : ℝ), ∃ c₂ : ℝ, ∀ᶠ n in atTop,
      ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₁ * n ^ (4 / 3 : ℝ) ≤ f d n ∧
      f d n ≤ ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 + c₂ * n ^ (4 / 3 : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example  (hd_odd : Odd d) :
    (5 ≤ d) ↔ (d ≥ 6) := by
  omega

set_option maxHeartbeats 200000 in
example  (hd_odd : Odd d) :
    (5 ≤ d) ↔ (d ≥ 6) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example  (hd_odd : Odd d) :
    (5 ≤ d) ↔ (d ≥ 6) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example  (hd_odd : Odd d) :
    (5 ≤ d) ↔ (d ≥ 6) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example  (hd_odd : Odd d) :
    (5 ≤ d) ↔ (d ≥ 6) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example  (hd_odd : Odd d) :
    (5 ≤ d) ↔ (d ≥ 6) := by
  simp_all

set_option maxHeartbeats 200000 in
example  (hd_odd : Odd d) :
    (5 ≤ d) ↔ (d ≥ 6) := by
  plausible

set_option maxHeartbeats 200000 in
example : (Odd d) ∧ (¬((5 ≤ d) ↔ (d ≥ 6))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (Odd d) ∧ (¬((5 ≤ d) ↔ (d ≥ 6))) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((5 ≤ d) ↔ (d ≥ 6)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((5 ≤ d) ↔ (d ≥ 6)) :=
  by decide

set_option maxHeartbeats 200000 in
example  (hd : 5 ≤ d) (hd_odd : Odd d) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example  (hd : 5 ≤ d) (hd_odd : Odd d) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example  (hd : 5 ≤ d) (hd_odd : Odd d) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example  (hd : 5 ≤ d) (hd_odd : Odd d) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example  (hd : 5 ≤ d) (hd_odd : Odd d) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
