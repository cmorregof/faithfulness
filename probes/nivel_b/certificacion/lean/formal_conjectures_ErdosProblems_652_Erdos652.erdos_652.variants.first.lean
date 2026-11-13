import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Geometry.Metric
--   notación `ℝ²` (scoped EuclideanGeometry, FCM.Geometry.2d)
/-!
# Erdős Problem 652

*References:*
- [erdosproblems.com/652](https://www.erdosproblems.com/652)
- [Ma21] Mathialagan, Surya, *On bipartite distinct distances in the plane*.
  Electron. J. Combin. **28** (2021), no. 4, Paper No. 4.33, 25 pp.
  [doi:10.37236/9687](https://doi.org/10.37236/9687)
- [Discussion](https://www.erdosproblems.com/forum/thread/652)
-/

section

open Filter
open scoped EuclideanGeometry

namespace Erdos652

open scoped Classical in
/-- The positive constants $a$ such that, for all sufficiently large $n$, some set of $n$
points has at least $k$ points determining fewer than $a\sqrt n$ distances to its other points.
Counting these points expresses $R(x_k)<a\sqrt n$ without choosing an ordering. -/
def AdmissibleConstant (k : ℕ) (a : ℝ) : Prop :=
  0 < a ∧ ∀ᶠ n : ℕ in atTop, ∃ points : Finset ℝ²,
    points.card = n ∧
      k ≤ (points.filter fun point => (distinctDistancesFrom points point : ℝ) <
        a * Real.sqrt n).card

/-- The infimum of the admissible positive constants for the $k$th smallest distance count.
An infimum is used because a least constant need not exist for a strict inequality. -/
noncomputable def alpha (k : ℕ) : ℝ :=
  sInf {a | AdmissibleConstant k a}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 < n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) →
    (∀ (n : ℕ) (hn : 2 < n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) →
    (∀ (n : ℕ) (hn : 2 < n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) →
    (∀ (n : ℕ) (hn : 2 < n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) →
    (∀ (n : ℕ) (hn : 2 < n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) →
    (∀ (n : ℕ) (hn : 2 < n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) →
    (∀ (n : ℕ) (hn : 2 < n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) →
    (∀ (n : ℕ) (hn : 2 < n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (2 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (2 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (2 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (2 < n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (2 < n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (2 < n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (2 < n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (2 < n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (2 < n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) →
    (∀ (n : ℕ) (hn : 3 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) →
    (∀ (n : ℕ) (hn : 3 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) →
    (∀ (n : ℕ) (hn : 3 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) →
    (∀ (n : ℕ) (hn : 3 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) →
    (∀ (n : ℕ) (hn : 3 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) →
    (∀ (n : ℕ) (hn : 3 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) →
    (∀ (n : ℕ) (hn : 3 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (3 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (3 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
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
  ∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 2), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (n ≥ 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (n ≥ 2) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (n ≥ 2) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (n ≥ 2) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (n ≥ 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (n ≥ 2) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (n ≥ 2) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (n ≥ 2) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) ↔
    (∀ (n : ℕ) (hn : n ≥ 2), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) ↔
    (∀ (n : ℕ) (hn : n ≥ 2), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) ↔
    (∀ (n : ℕ) (hn : n ≥ 2), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) ↔
    (∀ (n : ℕ) (hn : n ≥ 2), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn₀ : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) ↔
    (∀ (n : ℕ) (hn₀ : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) ↔
    (∀ (n : ℕ) (hn₀ : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) ↔
    (∀ (n : ℕ) (hn₀ : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) ↔
    (∀ (n : ℕ) (hn₀ : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : ¬(n < 2)), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) ↔
    (∀ (n : ℕ) (hn : ¬(n < 2)), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) ↔
    (∀ (n : ℕ) (hn : ¬(n < 2)), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) ↔
    (∀ (n : ℕ) (hn : ¬(n < 2)), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) ↔
    (∀ (n : ℕ) (hn : ¬(n < 2)), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (1 < n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (1 < n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (1 < n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (1 < n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (1 < n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (1 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (1 < n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (1 < n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) ↔
    (∀ (n : ℕ) (hn : 1 < n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) ↔
    (∀ (n : ℕ) (hn : 1 < n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) ↔
    (∀ (n : ℕ) (hn : 1 < n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) ↔
    (∀ (n : ℕ) (hn : 1 < n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 2), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) →
    (∀ (n : ℕ) (hn : n > 2), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) →
    (∀ (n : ℕ) (hn : n > 2), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) →
    (∀ (n : ℕ) (hn : n > 2), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) →
    (∀ (n : ℕ) (hn : n > 2), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) →
    (∀ (n : ℕ) (hn : n > 2), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) →
    (∀ (n : ℕ) (hn : n > 2), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) →
    (∀ (n : ℕ) (hn : n > 2), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n > 2) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n > 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n > 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n > 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n > 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n > 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n > 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n > 2))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n > 2))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n > 2))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n > 2))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n > 2))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n > 2))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n > 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n > 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n > 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n > 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n > 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n > 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 3), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) →
    (∀ (n : ℕ) (hn : n ≥ 3), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) →
    (∀ (n : ℕ) (hn : n ≥ 3), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) →
    (∀ (n : ℕ) (hn : n ≥ 3), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) →
    (∀ (n : ℕ) (hn : n ≥ 3), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) →
    (∀ (n : ℕ) (hn : n ≥ 3), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) →
    (∀ (n : ℕ) (hn : n ≥ 3), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) →
    (∀ (n : ℕ) (hn : n ≥ 3), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n ≥ 3) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n ≥ 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
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
  ∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) →
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) →
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) →
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) →
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) →
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) →
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) →
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ points : Finset ℝ², points.card = n ∧
      ∃ point ∈ points, distinctDistancesFrom points point = 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (1 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (1 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (1 ≤ n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (1 ≤ n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (1 ≤ n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (1 ≤ n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (1 ≤ n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (1 ≤ n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (1 ≤ n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (1 ≤ n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (1 ≤ n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (1 ≤ n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (1 ≤ n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (1 ≤ n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (1 ≤ n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 2 ≤ n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 2 ≤ n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 2 ≤ n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 2 ≤ n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 2 ≤ n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
