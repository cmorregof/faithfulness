import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Algebra.GCDMonoid.Finset
/-!
# Erdős Problem 678
*References:*
- [erdosproblems.com/678](https://www.erdosproblems.com/678)
- [Ca24] S. Cambie, Resolution of an Erdős' problem on least common multiples. arXiv:2410.09138
  (2024).
- [Er79] Erdős, Paul, Some unconventional problems in number theory. Math. Mag. (1979), 67-70.
- [Er92e] Erdős, Pál, Some Unsolved problems in Geometry, Number Theory and Combinatorics. Eureka
  (1992), 44-48.
-/

section

open Asymptotics Filter Finset

namespace Erdos678

set_option maxHeartbeats 200000 in
example : Prop :=
  lcmInterval 47 9 < lcmInterval 36 8

set_option maxHeartbeats 200000 in
example : Prop :=
  lcmInterval 47 9 ≤ lcmInterval 36 8

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) →
    (lcmInterval 47 9 ≤ lcmInterval 36 8) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) →
    (lcmInterval 47 9 ≤ lcmInterval 36 8) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) →
    (lcmInterval 47 9 ≤ lcmInterval 36 8) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) →
    (lcmInterval 47 9 ≤ lcmInterval 36 8) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) →
    (lcmInterval 47 9 ≤ lcmInterval 36 8) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) →
    (lcmInterval 47 9 ≤ lcmInterval 36 8) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) →
    (lcmInterval 47 9 ≤ lcmInterval 36 8) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ¬((lcmInterval 47 9 < lcmInterval 36 8) ↔ (lcmInterval 47 9 ≤ lcmInterval 36 8)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((lcmInterval 47 9 < lcmInterval 36 8) ↔ (lcmInterval 47 9 ≤ lcmInterval 36 8)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  lcmInterval 47 9 < lcmInterval 36 8

set_option maxHeartbeats 200000 in
example : Prop :=
  lcmInterval 47 10 < lcmInterval 36 8

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 10 < lcmInterval 36 8) →
    (lcmInterval 47 9 < lcmInterval 36 8) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 10 < lcmInterval 36 8) →
    (lcmInterval 47 9 < lcmInterval 36 8) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 10 < lcmInterval 36 8) →
    (lcmInterval 47 9 < lcmInterval 36 8) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 10 < lcmInterval 36 8) →
    (lcmInterval 47 9 < lcmInterval 36 8) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 10 < lcmInterval 36 8) →
    (lcmInterval 47 9 < lcmInterval 36 8) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 10 < lcmInterval 36 8) →
    (lcmInterval 47 9 < lcmInterval 36 8) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 10 < lcmInterval 36 8) →
    (lcmInterval 47 9 < lcmInterval 36 8) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) →
    (lcmInterval 47 10 < lcmInterval 36 8) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) →
    (lcmInterval 47 10 < lcmInterval 36 8) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) →
    (lcmInterval 47 10 < lcmInterval 36 8) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) →
    (lcmInterval 47 10 < lcmInterval 36 8) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) →
    (lcmInterval 47 10 < lcmInterval 36 8) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) →
    (lcmInterval 47 10 < lcmInterval 36 8) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) →
    (lcmInterval 47 10 < lcmInterval 36 8) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (¬(lcmInterval 47 10 < lcmInterval 36 8)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (¬(lcmInterval 47 10 < lcmInterval 36 8)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((lcmInterval 47 9 < lcmInterval 36 8) ↔ (lcmInterval 47 10 < lcmInterval 36 8)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((lcmInterval 47 9 < lcmInterval 36 8) ↔ (lcmInterval 47 10 < lcmInterval 36 8)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  lcmInterval 47 9 < lcmInterval 36 8

set_option maxHeartbeats 200000 in
example : Prop :=
  lcmInterval 47 9 > lcmInterval 36 8

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 > lcmInterval 36 8) →
    (lcmInterval 47 9 < lcmInterval 36 8) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 > lcmInterval 36 8) →
    (lcmInterval 47 9 < lcmInterval 36 8) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 > lcmInterval 36 8) →
    (lcmInterval 47 9 < lcmInterval 36 8) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 > lcmInterval 36 8) →
    (lcmInterval 47 9 < lcmInterval 36 8) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 > lcmInterval 36 8) →
    (lcmInterval 47 9 < lcmInterval 36 8) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 > lcmInterval 36 8) →
    (lcmInterval 47 9 < lcmInterval 36 8) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 > lcmInterval 36 8) →
    (lcmInterval 47 9 < lcmInterval 36 8) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) →
    (lcmInterval 47 9 > lcmInterval 36 8) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) →
    (lcmInterval 47 9 > lcmInterval 36 8) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) →
    (lcmInterval 47 9 > lcmInterval 36 8) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) →
    (lcmInterval 47 9 > lcmInterval 36 8) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) →
    (lcmInterval 47 9 > lcmInterval 36 8) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) →
    (lcmInterval 47 9 > lcmInterval 36 8) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) →
    (lcmInterval 47 9 > lcmInterval 36 8) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (¬(lcmInterval 47 9 > lcmInterval 36 8)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (¬(lcmInterval 47 9 > lcmInterval 36 8)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((lcmInterval 47 9 < lcmInterval 36 8) ↔ (lcmInterval 47 9 > lcmInterval 36 8)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((lcmInterval 47 9 < lcmInterval 36 8) ↔ (lcmInterval 47 9 > lcmInterval 36 8)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  lcmInterval 47 9 < lcmInterval 36 8

set_option maxHeartbeats 200000 in
example : Prop :=
  lcmInterval 36 8 > lcmInterval 47 9

set_option maxHeartbeats 200000 in
example  :
    (lcmInterval 47 9 < lcmInterval 36 8) ↔ (lcmInterval 36 8 > lcmInterval 47 9) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example  :
    (lcmInterval 47 9 < lcmInterval 36 8) ↔ (lcmInterval 36 8 > lcmInterval 47 9) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example  :
    (lcmInterval 47 9 < lcmInterval 36 8) ↔ (lcmInterval 36 8 > lcmInterval 47 9) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example  :
    (lcmInterval 47 9 < lcmInterval 36 8) ↔ (lcmInterval 36 8 > lcmInterval 47 9) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example  :
    (lcmInterval 47 9 < lcmInterval 36 8) ↔ (lcmInterval 36 8 > lcmInterval 47 9) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example  :
    (lcmInterval 47 9 < lcmInterval 36 8) ↔ (lcmInterval 36 8 > lcmInterval 47 9) := by
  omega

set_option maxHeartbeats 200000 in
example  :
    (lcmInterval 47 9 < lcmInterval 36 8) ↔ (lcmInterval 36 8 > lcmInterval 47 9) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example  :
    (lcmInterval 47 9 < lcmInterval 36 8) ↔ (lcmInterval 36 8 > lcmInterval 47 9) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) ↔
    (lcmInterval 36 8 > lcmInterval 47 9) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) ↔
    (lcmInterval 36 8 > lcmInterval 47 9) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) ↔
    (lcmInterval 36 8 > lcmInterval 47 9) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) ↔
    (lcmInterval 36 8 > lcmInterval 47 9) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  lcmInterval 47 9 < lcmInterval 36 8

set_option maxHeartbeats 200000 in
example : Prop :=
  ¬(lcmInterval 36 8 ≤ lcmInterval 47 9)

set_option maxHeartbeats 200000 in
example  :
    (lcmInterval 47 9 < lcmInterval 36 8) ↔ (¬(lcmInterval 36 8 ≤ lcmInterval 47 9)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example  :
    (lcmInterval 47 9 < lcmInterval 36 8) ↔ (¬(lcmInterval 36 8 ≤ lcmInterval 47 9)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example  :
    (lcmInterval 47 9 < lcmInterval 36 8) ↔ (¬(lcmInterval 36 8 ≤ lcmInterval 47 9)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example  :
    (lcmInterval 47 9 < lcmInterval 36 8) ↔ (¬(lcmInterval 36 8 ≤ lcmInterval 47 9)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example  :
    (lcmInterval 47 9 < lcmInterval 36 8) ↔ (¬(lcmInterval 36 8 ≤ lcmInterval 47 9)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example  :
    (lcmInterval 47 9 < lcmInterval 36 8) ↔ (¬(lcmInterval 36 8 ≤ lcmInterval 47 9)) := by
  omega

set_option maxHeartbeats 200000 in
example  :
    (lcmInterval 47 9 < lcmInterval 36 8) ↔ (¬(lcmInterval 36 8 ≤ lcmInterval 47 9)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example  :
    (lcmInterval 47 9 < lcmInterval 36 8) ↔ (¬(lcmInterval 36 8 ≤ lcmInterval 47 9)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) ↔
    (¬(lcmInterval 36 8 ≤ lcmInterval 47 9)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) ↔
    (¬(lcmInterval 36 8 ≤ lcmInterval 47 9)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) ↔
    (¬(lcmInterval 36 8 ≤ lcmInterval 47 9)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) ↔
    (¬(lcmInterval 36 8 ≤ lcmInterval 47 9)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  lcmInterval 47 9 < lcmInterval 36 8

set_option maxHeartbeats 200000 in
example : Prop :=
  lcmInterval 36 8 ≥ lcmInterval 47 9

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) →
    (lcmInterval 36 8 ≥ lcmInterval 47 9) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) →
    (lcmInterval 36 8 ≥ lcmInterval 47 9) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) →
    (lcmInterval 36 8 ≥ lcmInterval 47 9) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) →
    (lcmInterval 36 8 ≥ lcmInterval 47 9) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) →
    (lcmInterval 36 8 ≥ lcmInterval 47 9) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) →
    (lcmInterval 36 8 ≥ lcmInterval 47 9) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) →
    (lcmInterval 36 8 ≥ lcmInterval 47 9) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ¬((lcmInterval 47 9 < lcmInterval 36 8) ↔ (lcmInterval 36 8 ≥ lcmInterval 47 9)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((lcmInterval 47 9 < lcmInterval 36 8) ↔ (lcmInterval 36 8 ≥ lcmInterval 47 9)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  lcmInterval 47 9 < lcmInterval 36 8

set_option maxHeartbeats 200000 in
example : Prop :=
  lcmInterval 37 8 > lcmInterval 47 9

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 37 8 > lcmInterval 47 9) →
    (lcmInterval 47 9 < lcmInterval 36 8) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 37 8 > lcmInterval 47 9) →
    (lcmInterval 47 9 < lcmInterval 36 8) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 37 8 > lcmInterval 47 9) →
    (lcmInterval 47 9 < lcmInterval 36 8) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 37 8 > lcmInterval 47 9) →
    (lcmInterval 47 9 < lcmInterval 36 8) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 37 8 > lcmInterval 47 9) →
    (lcmInterval 47 9 < lcmInterval 36 8) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 37 8 > lcmInterval 47 9) →
    (lcmInterval 47 9 < lcmInterval 36 8) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 37 8 > lcmInterval 47 9) →
    (lcmInterval 47 9 < lcmInterval 36 8) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) →
    (lcmInterval 37 8 > lcmInterval 47 9) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) →
    (lcmInterval 37 8 > lcmInterval 47 9) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) →
    (lcmInterval 37 8 > lcmInterval 47 9) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) →
    (lcmInterval 37 8 > lcmInterval 47 9) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) →
    (lcmInterval 37 8 > lcmInterval 47 9) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) →
    (lcmInterval 37 8 > lcmInterval 47 9) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) →
    (lcmInterval 37 8 > lcmInterval 47 9) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (¬(lcmInterval 37 8 > lcmInterval 47 9)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (¬(lcmInterval 37 8 > lcmInterval 47 9)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((lcmInterval 47 9 < lcmInterval 36 8) ↔ (lcmInterval 37 8 > lcmInterval 47 9)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((lcmInterval 47 9 < lcmInterval 36 8) ↔ (lcmInterval 37 8 > lcmInterval 47 9)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  lcmInterval 47 9 < lcmInterval 36 8

set_option maxHeartbeats 200000 in
example : Prop :=
  lcmInterval 36 8 < lcmInterval 47 9

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 36 8 < lcmInterval 47 9) →
    (lcmInterval 47 9 < lcmInterval 36 8) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 36 8 < lcmInterval 47 9) →
    (lcmInterval 47 9 < lcmInterval 36 8) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 36 8 < lcmInterval 47 9) →
    (lcmInterval 47 9 < lcmInterval 36 8) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 36 8 < lcmInterval 47 9) →
    (lcmInterval 47 9 < lcmInterval 36 8) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 36 8 < lcmInterval 47 9) →
    (lcmInterval 47 9 < lcmInterval 36 8) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 36 8 < lcmInterval 47 9) →
    (lcmInterval 47 9 < lcmInterval 36 8) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 36 8 < lcmInterval 47 9) →
    (lcmInterval 47 9 < lcmInterval 36 8) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) →
    (lcmInterval 36 8 < lcmInterval 47 9) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) →
    (lcmInterval 36 8 < lcmInterval 47 9) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) →
    (lcmInterval 36 8 < lcmInterval 47 9) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) →
    (lcmInterval 36 8 < lcmInterval 47 9) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) →
    (lcmInterval 36 8 < lcmInterval 47 9) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) →
    (lcmInterval 36 8 < lcmInterval 47 9) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (lcmInterval 47 9 < lcmInterval 36 8) →
    (lcmInterval 36 8 < lcmInterval 47 9) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (¬(lcmInterval 36 8 < lcmInterval 47 9)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (¬(lcmInterval 36 8 < lcmInterval 47 9)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((lcmInterval 47 9 < lcmInterval 36 8) ↔ (lcmInterval 36 8 < lcmInterval 47 9)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((lcmInterval 47 9 < lcmInterval 36 8) ↔ (lcmInterval 36 8 < lcmInterval 47 9)) :=
  by decide

#eval "FIN_CERTIFICAR"
