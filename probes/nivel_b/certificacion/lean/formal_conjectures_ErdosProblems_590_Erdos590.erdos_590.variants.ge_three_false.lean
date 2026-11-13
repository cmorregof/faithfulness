import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.SetTheory.Cardinal.SimpleGraph
/-!
# Erdős Problem 590

*References:*
 - [erdosproblems.com/590](https://www.erdosproblems.com/590)
 - [Ch72] Chang, C. C., A partition theorem for the complete graph on {$\omega\sp{\omega }$}. J. Combinatorial Theory Ser. A (1972), 396-452.
 - [Sp57] Specker, Ernst, Teilmengen von Mengen mit Relationen. Comment. Math. Helv. (1957), 302-314.
 - [La73] Larson, Jean A., A short proof of a partition theorem for the ordinal {$\omega \sp{\omega }$}. Ann. Math. Logic (1973/74), 129-145.
-/

section

open Cardinal Ordinal

namespace Erdos590

universe u

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h : 3 < n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) →
    (∀ {n : ℕ} (h : 3 < n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) →
    (∀ {n : ℕ} (h : 3 < n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) →
    (∀ {n : ℕ} (h : 3 < n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) →
    (∀ {n : ℕ} (h : 3 < n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) →
    (∀ {n : ℕ} (h : 3 < n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) →
    (∀ {n : ℕ} (h : 3 < n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) →
    (∀ {n : ℕ} (h : 3 < n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
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
  ∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h : 4 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) →
    (∀ {n : ℕ} (h : 4 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) →
    (∀ {n : ℕ} (h : 4 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) →
    (∀ {n : ℕ} (h : 4 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) →
    (∀ {n : ℕ} (h : 4 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) →
    (∀ {n : ℕ} (h : 4 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) →
    (∀ {n : ℕ} (h : 4 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) →
    (∀ {n : ℕ} (h : 4 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
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
  ∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h : n ≥ 3), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3

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
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) ↔
    (∀ {n : ℕ} (h : n ≥ 3), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) ↔
    (∀ {n : ℕ} (h : n ≥ 3), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) ↔
    (∀ {n : ℕ} (h : n ≥ 3), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) ↔
    (∀ {n : ℕ} (h : n ≥ 3), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h₀ : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) ↔
    (∀ {n : ℕ} (h₀ : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) ↔
    (∀ {n : ℕ} (h₀ : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) ↔
    (∀ {n : ℕ} (h₀ : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) ↔
    (∀ {n : ℕ} (h₀ : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h : ¬(n < 3)), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3

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
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) ↔
    (∀ {n : ℕ} (h : ¬(n < 3)), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) ↔
    (∀ {n : ℕ} (h : ¬(n < 3)), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) ↔
    (∀ {n : ℕ} (h : ¬(n < 3)), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) ↔
    (∀ {n : ℕ} (h : ¬(n < 3)), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h : 2 < n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3

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
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) ↔
    (∀ {n : ℕ} (h : 2 < n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) ↔
    (∀ {n : ℕ} (h : 2 < n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) ↔
    (∀ {n : ℕ} (h : 2 < n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) ↔
    (∀ {n : ℕ} (h : 2 < n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h : n > 3), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) →
    (∀ {n : ℕ} (h : n > 3), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) →
    (∀ {n : ℕ} (h : n > 3), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) →
    (∀ {n : ℕ} (h : n > 3), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) →
    (∀ {n : ℕ} (h : n > 3), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) →
    (∀ {n : ℕ} (h : n > 3), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) →
    (∀ {n : ℕ} (h : n > 3), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) →
    (∀ {n : ℕ} (h : n > 3), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
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
  ∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h : n ≥ 4), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) →
    (∀ {n : ℕ} (h : n ≥ 4), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) →
    (∀ {n : ℕ} (h : n ≥ 4), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) →
    (∀ {n : ℕ} (h : n ≥ 4), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) →
    (∀ {n : ℕ} (h : n ≥ 4), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) →
    (∀ {n : ℕ} (h : n ≥ 4), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) →
    (∀ {n : ℕ} (h : n ≥ 4), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) →
    (∀ {n : ℕ} (h : n ≥ 4), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
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
  ∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h : 2 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 2 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) →
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 2 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) →
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 2 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) →
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 2 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) →
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 2 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) →
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 2 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) →
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 2 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) →
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
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
example : Prop :=
  ∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h : 2 < n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 4

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 2 < n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 4) →
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 2 < n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 4) →
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 2 < n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 4) →
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 2 < n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 4) →
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 2 < n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 4) →
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 2 < n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 4) →
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 2 < n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 4) →
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) →
    (∀ {n : ℕ} (h : 2 < n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 4) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) →
    (∀ {n : ℕ} (h : 2 < n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 4) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) →
    (∀ {n : ℕ} (h : 2 < n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 4) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) →
    (∀ {n : ℕ} (h : 2 < n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 4) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) →
    (∀ {n : ℕ} (h : 2 < n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 4) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) →
    (∀ {n : ℕ} (h : 2 < n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 4) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : 3 ≤ n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) →
    (∀ {n : ℕ} (h : 2 < n), ¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 4) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 4)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 4)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 4)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 4)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 4)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 4)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 4)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) ↔ (¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 4)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) ↔ (¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 4)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) ↔ (¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 4)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) ↔ (¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 4)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) ↔ (¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 4)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) ↔ (¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 4)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 3) ↔ (¬ OrdinalCardinalRamsey (ω ^ n) (ω ^ n) 4)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {n : ℕ} (h : 3 ≤ n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {n : ℕ} (h : 3 ≤ n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (h : 3 ≤ n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {n : ℕ} (h : 3 ≤ n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} (h : 3 ≤ n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
