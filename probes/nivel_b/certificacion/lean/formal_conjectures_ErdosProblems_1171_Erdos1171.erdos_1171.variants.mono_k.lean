import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.SetTheory.Ordinal.PartitionRelation
/-!
# Erdős Problem 1171

*Reference:* [erdosproblems.com/1171](https://www.erdosproblems.com/1171)
-/

section

open Cardinal Ordinal SimpleGraph

namespace Erdos1171

namespace erdos_1171.variants

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j

set_option maxHeartbeats 200000 in
example :
    (∀ {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) →
    (∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) →
    (∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) →
    (∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) →
    (∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) →
    (∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) →
    (∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) →
    (∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) :
    (j ≤ k) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) :
    (j ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) :
    (j ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) :
    (j ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) :
    (j ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) :
    (j ≤ k) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) :
    (j ≤ k) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {j k : ℕ} (hjk : j < k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j

set_option maxHeartbeats 200000 in
example :
    (∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) →
    (∀ {j k : ℕ} (hjk : j < k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) →
    (∀ {j k : ℕ} (hjk : j < k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) →
    (∀ {j k : ℕ} (hjk : j < k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) →
    (∀ {j k : ℕ} (hjk : j < k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) →
    (∀ {j k : ℕ} (hjk : j < k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) →
    (∀ {j k : ℕ} (hjk : j < k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) →
    (∀ {j k : ℕ} (hjk : j < k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) :
    (j ≤ k) ↔ (j < k) := by
  omega

set_option maxHeartbeats 200000 in
example {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) :
    (j ≤ k) ↔ (j < k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) :
    (j ≤ k) ↔ (j < k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) :
    (j ≤ k) ↔ (j < k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) :
    (j ≤ k) ↔ (j < k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) :
    (j ≤ k) ↔ (j < k) := by
  simp_all

set_option maxHeartbeats 200000 in
example {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) :
    (j ≤ k) ↔ (j < k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (j < k))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (j < k))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (j < k))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (j < k))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (j < k))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (j < k))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (j < k))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (j < k))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (j < k))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (j < k))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (j < k))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (j < k))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (j < k))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (j < k))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (j < k))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (j < k))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (j < k))) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (j < k))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (j < k))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (j < k))) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (j < k))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (j < k))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (j < k))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (j < k))) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (j < k))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (j < k))) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (j < k))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (j < k))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (j < k))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (j < k))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (j < k))) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (j < k))) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (j < k)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (j < k)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (j < k)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (j < k)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (j < k)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (j < k)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (j < k)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (j < k)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (j < k)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (j < k)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (j < k)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (j < k)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (j < k)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (j < k)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (j < k)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (j < k)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (j < k)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (j < k)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (j < k)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (j < k)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (j < k)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (j < k)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (j < k)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (j < k)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (j < k)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (j < k)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (j < k)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (j < k)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (j < k)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (j < k)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (j < k)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (j < k)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {j k : ℕ} (hjk : k ≥ j) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j

set_option maxHeartbeats 200000 in
example {j k : ℕ} :
    (j ≤ k) ↔ (k ≥ j) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {j k : ℕ} :
    (j ≤ k) ↔ (k ≥ j) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {j k : ℕ} :
    (j ≤ k) ↔ (k ≥ j) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {j k : ℕ} :
    (j ≤ k) ↔ (k ≥ j) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {j k : ℕ} :
    (j ≤ k) ↔ (k ≥ j) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {j k : ℕ} :
    (j ≤ k) ↔ (k ≥ j) := by
  omega

set_option maxHeartbeats 200000 in
example {j k : ℕ} :
    (j ≤ k) ↔ (k ≥ j) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {j k : ℕ} :
    (j ≤ k) ↔ (k ≥ j) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) ↔
    (∀ {j k : ℕ} (hjk : k ≥ j) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) ↔
    (∀ {j k : ℕ} (hjk : k ≥ j) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) ↔
    (∀ {j k : ℕ} (hjk : k ≥ j) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) ↔
    (∀ {j k : ℕ} (hjk : k ≥ j) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) (hjk : j ≤ k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j

set_option maxHeartbeats 200000 in
example :
    (∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) ↔
    (∀ {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) (hjk : j ≤ k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) ↔
    (∀ {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) (hjk : j ≤ k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) ↔
    (∀ {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) (hjk : j ≤ k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) ↔
    (∀ {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) (hjk : j ≤ k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {j k : ℕ} (hjk₀ : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j

set_option maxHeartbeats 200000 in
example :
    (∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) ↔
    (∀ {j k : ℕ} (hjk₀ : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) ↔
    (∀ {j k : ℕ} (hjk₀ : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) ↔
    (∀ {j k : ℕ} (hjk₀ : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) ↔
    (∀ {j k : ℕ} (hjk₀ : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {j k : ℕ} (hjk : ¬(k < j)) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j

set_option maxHeartbeats 200000 in
example {j k : ℕ} :
    (j ≤ k) ↔ (¬(k < j)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {j k : ℕ} :
    (j ≤ k) ↔ (¬(k < j)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {j k : ℕ} :
    (j ≤ k) ↔ (¬(k < j)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {j k : ℕ} :
    (j ≤ k) ↔ (¬(k < j)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {j k : ℕ} :
    (j ≤ k) ↔ (¬(k < j)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {j k : ℕ} :
    (j ≤ k) ↔ (¬(k < j)) := by
  omega

set_option maxHeartbeats 200000 in
example {j k : ℕ} :
    (j ≤ k) ↔ (¬(k < j)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {j k : ℕ} :
    (j ≤ k) ↔ (¬(k < j)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) ↔
    (∀ {j k : ℕ} (hjk : ¬(k < j)) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) ↔
    (∀ {j k : ℕ} (hjk : ¬(k < j)) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) ↔
    (∀ {j k : ℕ} (hjk : ¬(k < j)) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) ↔
    (∀ {j k : ℕ} (hjk : ¬(k < j)) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {j k : ℕ} (hjk : k > j) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j

set_option maxHeartbeats 200000 in
example :
    (∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) →
    (∀ {j k : ℕ} (hjk : k > j) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) →
    (∀ {j k : ℕ} (hjk : k > j) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) →
    (∀ {j k : ℕ} (hjk : k > j) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) →
    (∀ {j k : ℕ} (hjk : k > j) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) →
    (∀ {j k : ℕ} (hjk : k > j) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) →
    (∀ {j k : ℕ} (hjk : k > j) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) →
    (∀ {j k : ℕ} (hjk : k > j) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) :
    (j ≤ k) ↔ (k > j) := by
  omega

set_option maxHeartbeats 200000 in
example {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) :
    (j ≤ k) ↔ (k > j) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) :
    (j ≤ k) ↔ (k > j) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) :
    (j ≤ k) ↔ (k > j) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) :
    (j ≤ k) ↔ (k > j) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) :
    (j ≤ k) ↔ (k > j) := by
  simp_all

set_option maxHeartbeats 200000 in
example {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) :
    (j ≤ k) ↔ (k > j) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (k > j))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (k > j))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (k > j))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (k > j))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (k > j))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (k > j))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (k > j))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (k > j))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (k > j))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (k > j))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (k > j))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (k > j))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (k > j))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (k > j))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (k > j))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (k > j))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (k > j))) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (k > j))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (k > j))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (k > j))) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (k > j))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (k > j))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (k > j))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (k > j))) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (k > j))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (k > j))) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (k > j))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (k > j))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (k > j))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (k > j))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (k > j))) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (k > j))) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (k > j)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (k > j)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (k > j)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (k > j)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (k > j)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (k > j)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (k > j)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (k > j)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (k > j)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (k > j)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (k > j)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (k > j)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (k > j)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (k > j)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (k > j)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (k > j)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (k > j)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (k > j)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (k > j)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (k > j)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (k > j)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (k > j)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (k > j)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (k > j)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (k > j)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (k > j)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (k > j)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (k > j)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (k > j)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (k > j)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (k > j)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (k > j)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j

set_option maxHeartbeats 200000 in
example :
    (∀ {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) →
    (∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) →
    (∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) →
    (∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) →
    (∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) →
    (∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) →
    (∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) →
    (∀ {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k), OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) :
    (j ≤ k) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) :
    (j ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) :
    (j ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) :
    (j ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) :
    (j ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) :
    (j ≤ k) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) :
    (j ≤ k) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), (OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) ∧ (¬((j ≤ k) ↔ (True))) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (j : ℕ) (k : ℕ), ¬((j ≤ k) ↔ (True)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {j k : ℕ} (hjk : j ≤ k) (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
