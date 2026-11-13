import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   notación `ℝ²` (scoped EuclideanGeometry, FCM.Geometry.2d)
/-!
# Erdős Problem 214

*References:*
- [erdosproblems.com/214](https://www.erdosproblems.com/214)
- [CsTo94] Csizmadia, György and Tóth, Géza, *Note on a Ramsey-type problem in geometry*.
  J. Combin. Theory Ser. A (1994), 302-306.
- [EGMRSS75] Erdős, P. and Graham, R. L. and Montgomery, P. and Rothschild, B. L. and Spencer, J.
  and Straus, E. G., *Euclidean Ramsey theorems. II*. (1975), 529-557.
- [Ju79] Juhász, Rozália, *Ramsey type theorems in the plane*. J. Combin. Theory Ser. A (1979),
  152-160.
-/

section

open scoped Congruent EuclideanGeometry

namespace Erdos214

/-- The four vertices of a unit square. -/
def unitSquare : Fin 4 → ℝ² := ![!₂[0, 0], !₂[1, 0], !₂[1, 1], !₂[0, 1]]

/-- Colouring the points of `S` blue and the points of `Sᶜ` red gives a red/blue colouring of
$\mathbb{R}^2$; it is unit-distance-avoiding if no two blue points are distance $1$ apart. -/
def UnitDistanceAvoiding (S : Set ℝ²) : Prop := ∀ x ∈ S, ∀ y ∈ S, dist x y ≠ 1

/-- Any unit-distance-avoiding colouring contains a congruent red copy of every set of `n`
points. -/
def HasRedCopies (n : ℕ) : Prop :=
  ∀ S : Set ℝ², UnitDistanceAvoiding S → ∀ K : Fin n → ℝ², Function.Injective K →
    ∃ p : Fin n → ℝ², (∀ i, p i ∈ Sᶜ) ∧ (p ≅ K)

/-- The largest integer `k` such that any unit-distance-avoiding colouring contains a congruent
red copy of every set of `k` points. -/
noncomputable def k : ℕ := sSup {n | HasRedCopies n}

set_option maxHeartbeats 200000 in
example : Prop :=
  3 ≤ k ∧ k ≤ 10 ^ 12

set_option maxHeartbeats 200000 in
example : Prop :=
  3 ≤ k

set_option maxHeartbeats 200000 in
example :
    (3 ≤ k ∧ k ≤ 10 ^ 12) →
    (3 ≤ k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (3 ≤ k ∧ k ≤ 10 ^ 12) →
    (3 ≤ k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (3 ≤ k ∧ k ≤ 10 ^ 12) →
    (3 ≤ k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (3 ≤ k ∧ k ≤ 10 ^ 12) →
    (3 ≤ k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (3 ≤ k ∧ k ≤ 10 ^ 12) →
    (3 ≤ k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (3 ≤ k ∧ k ≤ 10 ^ 12) →
    (3 ≤ k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (3 ≤ k ∧ k ≤ 10 ^ 12) →
    (3 ≤ k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ¬((3 ≤ k ∧ k ≤ 10 ^ 12) ↔ (3 ≤ k)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((3 ≤ k ∧ k ≤ 10 ^ 12) ↔ (3 ≤ k)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  3 ≤ k ∧ k ≤ 10 ^ 12

set_option maxHeartbeats 200000 in
example : Prop :=
  4 ≤ k ∧ k ≤ 10 ^ 12

set_option maxHeartbeats 200000 in
example :
    (4 ≤ k ∧ k ≤ 10 ^ 12) →
    (3 ≤ k ∧ k ≤ 10 ^ 12) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (4 ≤ k ∧ k ≤ 10 ^ 12) →
    (3 ≤ k ∧ k ≤ 10 ^ 12) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (4 ≤ k ∧ k ≤ 10 ^ 12) →
    (3 ≤ k ∧ k ≤ 10 ^ 12) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (4 ≤ k ∧ k ≤ 10 ^ 12) →
    (3 ≤ k ∧ k ≤ 10 ^ 12) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (4 ≤ k ∧ k ≤ 10 ^ 12) →
    (3 ≤ k ∧ k ≤ 10 ^ 12) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (4 ≤ k ∧ k ≤ 10 ^ 12) →
    (3 ≤ k ∧ k ≤ 10 ^ 12) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (4 ≤ k ∧ k ≤ 10 ^ 12) →
    (3 ≤ k ∧ k ≤ 10 ^ 12) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (3 ≤ k ∧ k ≤ 10 ^ 12) →
    (4 ≤ k ∧ k ≤ 10 ^ 12) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (3 ≤ k ∧ k ≤ 10 ^ 12) →
    (4 ≤ k ∧ k ≤ 10 ^ 12) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (3 ≤ k ∧ k ≤ 10 ^ 12) →
    (4 ≤ k ∧ k ≤ 10 ^ 12) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (3 ≤ k ∧ k ≤ 10 ^ 12) →
    (4 ≤ k ∧ k ≤ 10 ^ 12) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (3 ≤ k ∧ k ≤ 10 ^ 12) →
    (4 ≤ k ∧ k ≤ 10 ^ 12) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (3 ≤ k ∧ k ≤ 10 ^ 12) →
    (4 ≤ k ∧ k ≤ 10 ^ 12) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (3 ≤ k ∧ k ≤ 10 ^ 12) →
    (4 ≤ k ∧ k ≤ 10 ^ 12) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (¬(4 ≤ k ∧ k ≤ 10 ^ 12)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (¬(4 ≤ k ∧ k ≤ 10 ^ 12)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((3 ≤ k ∧ k ≤ 10 ^ 12) ↔ (4 ≤ k ∧ k ≤ 10 ^ 12)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((3 ≤ k ∧ k ≤ 10 ^ 12) ↔ (4 ≤ k ∧ k ≤ 10 ^ 12)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  3 ≤ k ∧ k ≤ 10 ^ 12

set_option maxHeartbeats 200000 in
example : Prop :=
  k ≤ 10 ^ 12 ∧ 3 ≤ k

set_option maxHeartbeats 200000 in
example  :
    (3 ≤ k ∧ k ≤ 10 ^ 12) ↔ (k ≤ 10 ^ 12 ∧ 3 ≤ k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example  :
    (3 ≤ k ∧ k ≤ 10 ^ 12) ↔ (k ≤ 10 ^ 12 ∧ 3 ≤ k) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example  :
    (3 ≤ k ∧ k ≤ 10 ^ 12) ↔ (k ≤ 10 ^ 12 ∧ 3 ≤ k) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example  :
    (3 ≤ k ∧ k ≤ 10 ^ 12) ↔ (k ≤ 10 ^ 12 ∧ 3 ≤ k) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example  :
    (3 ≤ k ∧ k ≤ 10 ^ 12) ↔ (k ≤ 10 ^ 12 ∧ 3 ≤ k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example  :
    (3 ≤ k ∧ k ≤ 10 ^ 12) ↔ (k ≤ 10 ^ 12 ∧ 3 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example  :
    (3 ≤ k ∧ k ≤ 10 ^ 12) ↔ (k ≤ 10 ^ 12 ∧ 3 ≤ k) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example  :
    (3 ≤ k ∧ k ≤ 10 ^ 12) ↔ (k ≤ 10 ^ 12 ∧ 3 ≤ k) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (3 ≤ k ∧ k ≤ 10 ^ 12) ↔
    (k ≤ 10 ^ 12 ∧ 3 ≤ k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (3 ≤ k ∧ k ≤ 10 ^ 12) ↔
    (k ≤ 10 ^ 12 ∧ 3 ≤ k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (3 ≤ k ∧ k ≤ 10 ^ 12) ↔
    (k ≤ 10 ^ 12 ∧ 3 ≤ k) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (3 ≤ k ∧ k ≤ 10 ^ 12) ↔
    (k ≤ 10 ^ 12 ∧ 3 ≤ k) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  3 ≤ k ∧ k ≤ 10 ^ 12

set_option maxHeartbeats 200000 in
example : Prop :=
  k ≤ 10 ^ 12

set_option maxHeartbeats 200000 in
example :
    (3 ≤ k ∧ k ≤ 10 ^ 12) →
    (k ≤ 10 ^ 12) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (3 ≤ k ∧ k ≤ 10 ^ 12) →
    (k ≤ 10 ^ 12) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (3 ≤ k ∧ k ≤ 10 ^ 12) →
    (k ≤ 10 ^ 12) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (3 ≤ k ∧ k ≤ 10 ^ 12) →
    (k ≤ 10 ^ 12) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (3 ≤ k ∧ k ≤ 10 ^ 12) →
    (k ≤ 10 ^ 12) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (3 ≤ k ∧ k ≤ 10 ^ 12) →
    (k ≤ 10 ^ 12) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (3 ≤ k ∧ k ≤ 10 ^ 12) →
    (k ≤ 10 ^ 12) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ¬((3 ≤ k ∧ k ≤ 10 ^ 12) ↔ (k ≤ 10 ^ 12)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((3 ≤ k ∧ k ≤ 10 ^ 12) ↔ (k ≤ 10 ^ 12)) :=
  by decide

#eval "FIN_CERTIFICAR"
