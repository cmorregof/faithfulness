import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Geometry.2d
--   notación `ℝ²` (scoped EuclideanGeometry, FCM.Geometry.2d)
/-!
# Erdős Problem 107

*References:*
- [erdosproblems.com/107](https://www.erdosproblems.com/107)
- [Wikipedia](https://en.wikipedia.org/wiki/Happy_ending_problem)
-/

section

open Filter
open EuclideanGeometry

namespace Erdos107

/-- The set of $N$ such that any $N$ points in the plane, no three on a line,
contain a convex $n$-gon. -/
def cardSet (n : ℕ) := { N | ∀ (pts : Finset ℝ²), pts.card = N → NonTrilinear (pts : Set ℝ²) →
  HasConvexNGon n pts }

/-- The function $f(n)$ specified in `erdos_107`. -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf (cardSet n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℝ²} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℝ²} (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℝ²} (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) →
    (∀ {a b c : ℝ²} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℝ²} (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) →
    (∀ {a b c : ℝ²} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℝ²} (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) →
    (∀ {a b c : ℝ²} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℝ²} (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) →
    (∀ {a b c : ℝ²} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℝ²} (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) →
    (∀ {a b c : ℝ²} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℝ²} (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) →
    (∀ {a b c : ℝ²} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℝ²} (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) →
    (∀ {a b c : ℝ²} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {a b c : ℝ²} (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)) :
    (a ≠ b) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {a b c : ℝ²} (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)) :
    (a ≠ b) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {a b c : ℝ²} (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)) :
    (a ≠ b) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {a b c : ℝ²} (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)) :
    (a ≠ b) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {a b c : ℝ²} (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)) :
    (a ≠ b) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {a b c : ℝ²} (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)) :
    (a ≠ b) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {a b c : ℝ²} (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)) :
    (a ≠ b) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℝ²} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℝ²} (hab : ¬(a = b)) (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)

set_option maxHeartbeats 200000 in
example {a b c : ℝ²} :
    (a ≠ b) ↔ (¬(a = b)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {a b c : ℝ²} :
    (a ≠ b) ↔ (¬(a = b)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {a b c : ℝ²} :
    (a ≠ b) ↔ (¬(a = b)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {a b c : ℝ²} :
    (a ≠ b) ↔ (¬(a = b)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {a b c : ℝ²} :
    (a ≠ b) ↔ (¬(a = b)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {a b c : ℝ²} :
    (a ≠ b) ↔ (¬(a = b)) := by
  omega

set_option maxHeartbeats 200000 in
example {a b c : ℝ²} :
    (a ≠ b) ↔ (¬(a = b)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {a b c : ℝ²} :
    (a ≠ b) ↔ (¬(a = b)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℝ²} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) ↔
    (∀ {a b c : ℝ²} (hab : ¬(a = b)) (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℝ²} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) ↔
    (∀ {a b c : ℝ²} (hab : ¬(a = b)) (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℝ²} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) ↔
    (∀ {a b c : ℝ²} (hab : ¬(a = b)) (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℝ²} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) ↔
    (∀ {a b c : ℝ²} (hab : ¬(a = b)) (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℝ²} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℝ²} (hac : a ≠ c) (hab : a ≠ b) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℝ²} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) ↔
    (∀ {a b c : ℝ²} (hac : a ≠ c) (hab : a ≠ b) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℝ²} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) ↔
    (∀ {a b c : ℝ²} (hac : a ≠ c) (hab : a ≠ b) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℝ²} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) ↔
    (∀ {a b c : ℝ²} (hac : a ≠ c) (hab : a ≠ b) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℝ²} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) ↔
    (∀ {a b c : ℝ²} (hac : a ≠ c) (hab : a ≠ b) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℝ²} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℝ²} (hab₀ : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℝ²} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) ↔
    (∀ {a b c : ℝ²} (hab₀ : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℝ²} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) ↔
    (∀ {a b c : ℝ²} (hab₀ : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℝ²} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) ↔
    (∀ {a b c : ℝ²} (hab₀ : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℝ²} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) ↔
    (∀ {a b c : ℝ²} (hab₀ : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℝ²} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℝ²} (hab : a ≠ b) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℝ²} (hab : a ≠ b) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) →
    (∀ {a b c : ℝ²} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℝ²} (hab : a ≠ b) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) →
    (∀ {a b c : ℝ²} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℝ²} (hab : a ≠ b) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) →
    (∀ {a b c : ℝ²} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℝ²} (hab : a ≠ b) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) →
    (∀ {a b c : ℝ²} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℝ²} (hab : a ≠ b) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) →
    (∀ {a b c : ℝ²} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℝ²} (hab : a ≠ b) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) →
    (∀ {a b c : ℝ²} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℝ²} (hab : a ≠ b) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) →
    (∀ {a b c : ℝ²} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)), ConvexIndep ({a, b, c} : Set ℝ²)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {a b c : ℝ²} (hab : a ≠ b) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)) :
    (a ≠ c) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {a b c : ℝ²} (hab : a ≠ b) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)) :
    (a ≠ c) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {a b c : ℝ²} (hab : a ≠ b) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)) :
    (a ≠ c) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {a b c : ℝ²} (hab : a ≠ b) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)) :
    (a ≠ c) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {a b c : ℝ²} (hab : a ≠ b) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)) :
    (a ≠ c) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {a b c : ℝ²} (hab : a ≠ b) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)) :
    (a ≠ c) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {a b c : ℝ²} (hab : a ≠ b) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)) :
    (a ≠ c) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example {a b c : ℝ²} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {a b c : ℝ²} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {a b c : ℝ²} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {a b c : ℝ²} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {a b c : ℝ²} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hcoll : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
