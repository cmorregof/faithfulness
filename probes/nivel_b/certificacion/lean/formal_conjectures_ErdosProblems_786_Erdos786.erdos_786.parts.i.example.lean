import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Data.Set.Density
/-!
# Erdős Problem 786

*Reference:* [erdosproblems.com/786](https://www.erdosproblems.com/786)
-/

section

open Filter Real

open scoped Topology

namespace Erdos786

open Erdos786

-- TODO : add variants that allow repetition.
-- According to the updated website, Erdos likely intended repetitions to be allowed here
-- however, the analogous questions without repetition are also open.
/--
`Nat.IsMulCardSet A` means that `A` is a set of natural numbers that
satisfies the property that $a_1\cdots a_r = b_1\cdots b_s$ with $a_i, b_j\in A$
can only hold when $r = s$.
-/
def Set.IsMulCardSet {α : Type*} [CommMonoid α] (A : Set α) :=
  ∀ (a b : Finset α) (_ :↑a ⊆ A) (_ : ↑b ⊆ A) (_ : a.prod id = b.prod id),
    a.card = b.card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Set ℕ) (hA : A = { n | n % 4 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Set ℕ) (hA : A = { n | n % 5 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : A = { n | n % 5 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) →
    (∀ (A : Set ℕ) (hA : A = { n | n % 4 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : A = { n | n % 5 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) →
    (∀ (A : Set ℕ) (hA : A = { n | n % 4 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : A = { n | n % 5 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) →
    (∀ (A : Set ℕ) (hA : A = { n | n % 4 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : A = { n | n % 5 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) →
    (∀ (A : Set ℕ) (hA : A = { n | n % 4 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : A = { n | n % 5 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) →
    (∀ (A : Set ℕ) (hA : A = { n | n % 4 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : A = { n | n % 5 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) →
    (∀ (A : Set ℕ) (hA : A = { n | n % 4 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : A = { n | n % 5 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) →
    (∀ (A : Set ℕ) (hA : A = { n | n % 4 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : A = { n | n % 4 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) →
    (∀ (A : Set ℕ) (hA : A = { n | n % 5 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : A = { n | n % 4 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) →
    (∀ (A : Set ℕ) (hA : A = { n | n % 5 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : A = { n | n % 4 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) →
    (∀ (A : Set ℕ) (hA : A = { n | n % 5 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : A = { n | n % 4 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) →
    (∀ (A : Set ℕ) (hA : A = { n | n % 5 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : A = { n | n % 4 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) →
    (∀ (A : Set ℕ) (hA : A = { n | n % 5 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : A = { n | n % 4 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) →
    (∀ (A : Set ℕ) (hA : A = { n | n % 5 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : A = { n | n % 4 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) →
    (∀ (A : Set ℕ) (hA : A = { n | n % 5 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (A : Set ℕ)  :
    (A = { n | n % 4 = 2 }) ↔ (A = { n | n % 5 = 2 }) := by
  omega

set_option maxHeartbeats 200000 in
example (A : Set ℕ)  :
    (A = { n | n % 4 = 2 }) ↔ (A = { n | n % 5 = 2 }) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (A : Set ℕ)  :
    (A = { n | n % 4 = 2 }) ↔ (A = { n | n % 5 = 2 }) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (A : Set ℕ)  :
    (A = { n | n % 4 = 2 }) ↔ (A = { n | n % 5 = 2 }) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (A : Set ℕ)  :
    (A = { n | n % 4 = 2 }) ↔ (A = { n | n % 5 = 2 }) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (A : Set ℕ)  :
    (A = { n | n % 4 = 2 }) ↔ (A = { n | n % 5 = 2 }) := by
  simp_all

set_option maxHeartbeats 200000 in
example (A : Set ℕ)  :
    (A = { n | n % 4 = 2 }) ↔ (A = { n | n % 5 = 2 }) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Set ℕ) (hA : A = { n | n % 4 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Set ℕ) (hA : A = { n | n % 4 = 2 }), A.IsMulCardSet ∧ A.HasDensity (1 / 4)

set_option maxHeartbeats 200000 in
example (A : Set ℕ) :
    (A.HasDensity (1 / 4) ∧ A.IsMulCardSet) ↔ (A.IsMulCardSet ∧ A.HasDensity (1 / 4)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (A : Set ℕ) :
    (A.HasDensity (1 / 4) ∧ A.IsMulCardSet) ↔ (A.IsMulCardSet ∧ A.HasDensity (1 / 4)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (A : Set ℕ) :
    (A.HasDensity (1 / 4) ∧ A.IsMulCardSet) ↔ (A.IsMulCardSet ∧ A.HasDensity (1 / 4)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (A : Set ℕ) :
    (A.HasDensity (1 / 4) ∧ A.IsMulCardSet) ↔ (A.IsMulCardSet ∧ A.HasDensity (1 / 4)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (A : Set ℕ) :
    (A.HasDensity (1 / 4) ∧ A.IsMulCardSet) ↔ (A.IsMulCardSet ∧ A.HasDensity (1 / 4)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (A : Set ℕ) :
    (A.HasDensity (1 / 4) ∧ A.IsMulCardSet) ↔ (A.IsMulCardSet ∧ A.HasDensity (1 / 4)) := by
  omega

set_option maxHeartbeats 200000 in
example (A : Set ℕ) :
    (A.HasDensity (1 / 4) ∧ A.IsMulCardSet) ↔ (A.IsMulCardSet ∧ A.HasDensity (1 / 4)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (A : Set ℕ) :
    (A.HasDensity (1 / 4) ∧ A.IsMulCardSet) ↔ (A.IsMulCardSet ∧ A.HasDensity (1 / 4)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : A = { n | n % 4 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) ↔
    (∀ (A : Set ℕ) (hA : A = { n | n % 4 = 2 }), A.IsMulCardSet ∧ A.HasDensity (1 / 4)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : A = { n | n % 4 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) ↔
    (∀ (A : Set ℕ) (hA : A = { n | n % 4 = 2 }), A.IsMulCardSet ∧ A.HasDensity (1 / 4)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : A = { n | n % 4 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) ↔
    (∀ (A : Set ℕ) (hA : A = { n | n % 4 = 2 }), A.IsMulCardSet ∧ A.HasDensity (1 / 4)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : A = { n | n % 4 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) ↔
    (∀ (A : Set ℕ) (hA : A = { n | n % 4 = 2 }), A.IsMulCardSet ∧ A.HasDensity (1 / 4)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Set ℕ) (hA : A = { n | n % 4 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Set ℕ) (hA₀ : A = { n | n % 4 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : A = { n | n % 4 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) ↔
    (∀ (A : Set ℕ) (hA₀ : A = { n | n % 4 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : A = { n | n % 4 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) ↔
    (∀ (A : Set ℕ) (hA₀ : A = { n | n % 4 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : A = { n | n % 4 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) ↔
    (∀ (A : Set ℕ) (hA₀ : A = { n | n % 4 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : A = { n | n % 4 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) ↔
    (∀ (A : Set ℕ) (hA₀ : A = { n | n % 4 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Set ℕ) (hA : A = { n | n % 4 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Set ℕ) (hA : A = { n | n % 4 = 2 }), A.IsMulCardSet

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : A = { n | n % 4 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) →
    (∀ (A : Set ℕ) (hA : A = { n | n % 4 = 2 }), A.IsMulCardSet) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : A = { n | n % 4 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) →
    (∀ (A : Set ℕ) (hA : A = { n | n % 4 = 2 }), A.IsMulCardSet) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : A = { n | n % 4 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) →
    (∀ (A : Set ℕ) (hA : A = { n | n % 4 = 2 }), A.IsMulCardSet) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : A = { n | n % 4 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) →
    (∀ (A : Set ℕ) (hA : A = { n | n % 4 = 2 }), A.IsMulCardSet) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : A = { n | n % 4 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) →
    (∀ (A : Set ℕ) (hA : A = { n | n % 4 = 2 }), A.IsMulCardSet) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : A = { n | n % 4 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) →
    (∀ (A : Set ℕ) (hA : A = { n | n % 4 = 2 }), A.IsMulCardSet) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Set ℕ) (hA : A = { n | n % 4 = 2 }), A.HasDensity (1 / 4) ∧ A.IsMulCardSet) →
    (∀ (A : Set ℕ) (hA : A = { n | n % 4 = 2 }), A.IsMulCardSet) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (A : Set ℕ) (hA : A = { n | n % 4 = 2 }) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (A : Set ℕ) (hA : A = { n | n % 4 = 2 }) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (A : Set ℕ) (hA : A = { n | n % 4 = 2 }) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (A : Set ℕ) (hA : A = { n | n % 4 = 2 }) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (A : Set ℕ) (hA : A = { n | n % 4 = 2 }) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
