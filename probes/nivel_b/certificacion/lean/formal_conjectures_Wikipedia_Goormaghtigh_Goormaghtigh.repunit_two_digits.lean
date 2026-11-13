import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# The Goormaghtigh conjecture

A repunit is a number whose digits in some base are all $1$. Here a nontrivial representation has
at least three digits. The Goormaghtigh conjecture says that $31$ and $8191$ are the only numbers
having nontrivial repunit representations in two different bases.

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Goormaghtigh_conjecture)
* J. Grantham,
  [No new Goormaghtigh primes up to $10^{700}$](https://math.colgate.edu/~integers/y98/y98.pdf)
-/

section

namespace Goormaghtigh

/-- The repunit with `digits` digits in the given base, expressed without division. -/
def repunit (base digits : ℕ) : ℕ :=
  ∑ i ∈ Finset.range digits, base ^ i

/-- A number having repunit representations of at least three digits in two distinct bases. -/
def IsGoormaghtighNumber (N : ℕ) : Prop :=
  ∃ base₁ base₂ digits₁ digits₂ : ℕ,
    2 ≤ base₁ ∧ 2 ≤ base₂ ∧ base₁ ≠ base₂ ∧
      3 ≤ digits₁ ∧ 3 ≤ digits₂ ∧
        repunit base₁ digits₁ = N ∧ repunit base₂ digits₂ = N

set_option maxHeartbeats 200000 in
example : Prop :=
  repunit 3 3 = 13 ∧ repunit 12 2 = 13

set_option maxHeartbeats 200000 in
example : Prop :=
  repunit 3 3 = 13

set_option maxHeartbeats 200000 in
example :
    (repunit 3 3 = 13 ∧ repunit 12 2 = 13) →
    (repunit 3 3 = 13) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (repunit 3 3 = 13 ∧ repunit 12 2 = 13) →
    (repunit 3 3 = 13) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (repunit 3 3 = 13 ∧ repunit 12 2 = 13) →
    (repunit 3 3 = 13) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (repunit 3 3 = 13 ∧ repunit 12 2 = 13) →
    (repunit 3 3 = 13) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (repunit 3 3 = 13 ∧ repunit 12 2 = 13) →
    (repunit 3 3 = 13) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (repunit 3 3 = 13 ∧ repunit 12 2 = 13) →
    (repunit 3 3 = 13) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (repunit 3 3 = 13 ∧ repunit 12 2 = 13) →
    (repunit 3 3 = 13) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ¬((repunit 3 3 = 13 ∧ repunit 12 2 = 13) ↔ (repunit 3 3 = 13)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((repunit 3 3 = 13 ∧ repunit 12 2 = 13) ↔ (repunit 3 3 = 13)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  repunit 3 3 = 13 ∧ repunit 12 2 = 13

set_option maxHeartbeats 200000 in
example : Prop :=
  repunit 3 3 = 14 ∧ repunit 12 2 = 13

set_option maxHeartbeats 200000 in
example :
    (repunit 3 3 = 14 ∧ repunit 12 2 = 13) →
    (repunit 3 3 = 13 ∧ repunit 12 2 = 13) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (repunit 3 3 = 14 ∧ repunit 12 2 = 13) →
    (repunit 3 3 = 13 ∧ repunit 12 2 = 13) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (repunit 3 3 = 14 ∧ repunit 12 2 = 13) →
    (repunit 3 3 = 13 ∧ repunit 12 2 = 13) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (repunit 3 3 = 14 ∧ repunit 12 2 = 13) →
    (repunit 3 3 = 13 ∧ repunit 12 2 = 13) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (repunit 3 3 = 14 ∧ repunit 12 2 = 13) →
    (repunit 3 3 = 13 ∧ repunit 12 2 = 13) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (repunit 3 3 = 14 ∧ repunit 12 2 = 13) →
    (repunit 3 3 = 13 ∧ repunit 12 2 = 13) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (repunit 3 3 = 14 ∧ repunit 12 2 = 13) →
    (repunit 3 3 = 13 ∧ repunit 12 2 = 13) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (repunit 3 3 = 13 ∧ repunit 12 2 = 13) →
    (repunit 3 3 = 14 ∧ repunit 12 2 = 13) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (repunit 3 3 = 13 ∧ repunit 12 2 = 13) →
    (repunit 3 3 = 14 ∧ repunit 12 2 = 13) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (repunit 3 3 = 13 ∧ repunit 12 2 = 13) →
    (repunit 3 3 = 14 ∧ repunit 12 2 = 13) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (repunit 3 3 = 13 ∧ repunit 12 2 = 13) →
    (repunit 3 3 = 14 ∧ repunit 12 2 = 13) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (repunit 3 3 = 13 ∧ repunit 12 2 = 13) →
    (repunit 3 3 = 14 ∧ repunit 12 2 = 13) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (repunit 3 3 = 13 ∧ repunit 12 2 = 13) →
    (repunit 3 3 = 14 ∧ repunit 12 2 = 13) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (repunit 3 3 = 13 ∧ repunit 12 2 = 13) →
    (repunit 3 3 = 14 ∧ repunit 12 2 = 13) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (¬(repunit 3 3 = 14 ∧ repunit 12 2 = 13)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (¬(repunit 3 3 = 14 ∧ repunit 12 2 = 13)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((repunit 3 3 = 13 ∧ repunit 12 2 = 13) ↔ (repunit 3 3 = 14 ∧ repunit 12 2 = 13)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((repunit 3 3 = 13 ∧ repunit 12 2 = 13) ↔ (repunit 3 3 = 14 ∧ repunit 12 2 = 13)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  repunit 3 3 = 13 ∧ repunit 12 2 = 13

set_option maxHeartbeats 200000 in
example : Prop :=
  repunit 12 2 = 13 ∧ repunit 3 3 = 13

set_option maxHeartbeats 200000 in
example  :
    (repunit 3 3 = 13 ∧ repunit 12 2 = 13) ↔ (repunit 12 2 = 13 ∧ repunit 3 3 = 13) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example  :
    (repunit 3 3 = 13 ∧ repunit 12 2 = 13) ↔ (repunit 12 2 = 13 ∧ repunit 3 3 = 13) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example  :
    (repunit 3 3 = 13 ∧ repunit 12 2 = 13) ↔ (repunit 12 2 = 13 ∧ repunit 3 3 = 13) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example  :
    (repunit 3 3 = 13 ∧ repunit 12 2 = 13) ↔ (repunit 12 2 = 13 ∧ repunit 3 3 = 13) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example  :
    (repunit 3 3 = 13 ∧ repunit 12 2 = 13) ↔ (repunit 12 2 = 13 ∧ repunit 3 3 = 13) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example  :
    (repunit 3 3 = 13 ∧ repunit 12 2 = 13) ↔ (repunit 12 2 = 13 ∧ repunit 3 3 = 13) := by
  omega

set_option maxHeartbeats 200000 in
example  :
    (repunit 3 3 = 13 ∧ repunit 12 2 = 13) ↔ (repunit 12 2 = 13 ∧ repunit 3 3 = 13) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example  :
    (repunit 3 3 = 13 ∧ repunit 12 2 = 13) ↔ (repunit 12 2 = 13 ∧ repunit 3 3 = 13) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (repunit 3 3 = 13 ∧ repunit 12 2 = 13) ↔
    (repunit 12 2 = 13 ∧ repunit 3 3 = 13) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (repunit 3 3 = 13 ∧ repunit 12 2 = 13) ↔
    (repunit 12 2 = 13 ∧ repunit 3 3 = 13) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (repunit 3 3 = 13 ∧ repunit 12 2 = 13) ↔
    (repunit 12 2 = 13 ∧ repunit 3 3 = 13) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (repunit 3 3 = 13 ∧ repunit 12 2 = 13) ↔
    (repunit 12 2 = 13 ∧ repunit 3 3 = 13) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  repunit 3 3 = 13 ∧ repunit 12 2 = 13

set_option maxHeartbeats 200000 in
example : Prop :=
  repunit 12 2 = 13

set_option maxHeartbeats 200000 in
example :
    (repunit 3 3 = 13 ∧ repunit 12 2 = 13) →
    (repunit 12 2 = 13) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (repunit 3 3 = 13 ∧ repunit 12 2 = 13) →
    (repunit 12 2 = 13) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (repunit 3 3 = 13 ∧ repunit 12 2 = 13) →
    (repunit 12 2 = 13) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (repunit 3 3 = 13 ∧ repunit 12 2 = 13) →
    (repunit 12 2 = 13) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (repunit 3 3 = 13 ∧ repunit 12 2 = 13) →
    (repunit 12 2 = 13) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (repunit 3 3 = 13 ∧ repunit 12 2 = 13) →
    (repunit 12 2 = 13) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (repunit 3 3 = 13 ∧ repunit 12 2 = 13) →
    (repunit 12 2 = 13) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ¬((repunit 3 3 = 13 ∧ repunit 12 2 = 13) ↔ (repunit 12 2 = 13)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((repunit 3 3 = 13 ∧ repunit 12 2 = 13) ↔ (repunit 12 2 = 13)) :=
  by decide

#eval "FIN_CERTIFICAR"
