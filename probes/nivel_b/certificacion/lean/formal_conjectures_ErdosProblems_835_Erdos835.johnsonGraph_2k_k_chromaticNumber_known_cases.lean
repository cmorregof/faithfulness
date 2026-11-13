import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   notación `J(n, k)` (FCM.Combinatorics.SimpleGraph.Johnson)
/-!
# Erdős Problem 835

*References:*
 - [erdosproblems.com/835](https://www.erdosproblems.com/835)
 - [MT25](https://github.com/QuanyuTang/erdos-problem-835/blob/main/On_Problem_835.pdf)
-/

section

open Finset SimpleGraph
open scoped Nat
namespace Erdos835

variable {n k : ℕ}

/--
The property that for a given $k$, the $k$-subsets of a $2k$-set can be colored with $k+1$ colors
such that any $(k+1)$-subset contains all colors.
-/
def Property (k : ℕ) : Prop :=
  let K := {s : Finset (Fin (2 * k)) // s.card = k}
  ∃ c : K → Fin (k + 1),
    ∀ A : Finset (Fin (2 * k)), A.card = k + 1 →
      (image c {s : K | s.val ⊂ A}) = (univ : Finset (Fin (k+1)))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk' : k ≤ 8) :
    (3 ≤ k) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk' : k ≤ 8) :
    (3 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk' : k ≤ 8) :
    (3 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk' : k ≤ 8) :
    (3 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk' : k ≤ 8) :
    (3 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk' : k ≤ 8) :
    (3 ≤ k) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk' : k ≤ 8) :
    (3 ≤ k) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (True))) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (True))) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (True))) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (True))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (True))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (True))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (True))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (True))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (True))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (True))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (True)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber ≥ k + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber ≥ k + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber ≥ k + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber ≥ k + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber ≥ k + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber ≥ k + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber ≥ k + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber ≥ k + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((J(2 * k, k).chromaticNumber > k + 1) ↔ (J(2 * k, k).chromaticNumber ≥ k + 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((J(2 * k, k).chromaticNumber > k + 1) ↔ (J(2 * k, k).chromaticNumber ≥ k + 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((J(2 * k, k).chromaticNumber > k + 1) ↔ (J(2 * k, k).chromaticNumber ≥ k + 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((J(2 * k, k).chromaticNumber > k + 1) ↔ (J(2 * k, k).chromaticNumber ≥ k + 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((J(2 * k, k).chromaticNumber > k + 1) ↔ (J(2 * k, k).chromaticNumber ≥ k + 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((J(2 * k, k).chromaticNumber > k + 1) ↔ (J(2 * k, k).chromaticNumber ≥ k + 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 < k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 3 < k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 3 < k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 3 < k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 3 < k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 3 < k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 3 < k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 3 < k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk' : k ≤ 8) :
    (3 ≤ k) ↔ (3 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk' : k ≤ 8) :
    (3 ≤ k) ↔ (3 < k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk' : k ≤ 8) :
    (3 ≤ k) ↔ (3 < k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk' : k ≤ 8) :
    (3 ≤ k) ↔ (3 < k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk' : k ≤ 8) :
    (3 ≤ k) ↔ (3 < k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk' : k ≤ 8) :
    (3 ≤ k) ↔ (3 < k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk' : k ≤ 8) :
    (3 ≤ k) ↔ (3 < k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (3 < k))) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (3 < k))) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (3 < k))) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (3 < k))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (3 < k))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (3 < k))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (3 < k))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (3 < k))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (3 < k))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (3 < k))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (3 < k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (3 < k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (3 < k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (3 < k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (3 < k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (3 < k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (3 < k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk' : k ≤ 8) :
    (3 ≤ k) ↔ (4 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk' : k ≤ 8) :
    (3 ≤ k) ↔ (4 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk' : k ≤ 8) :
    (3 ≤ k) ↔ (4 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk' : k ≤ 8) :
    (3 ≤ k) ↔ (4 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk' : k ≤ 8) :
    (3 ≤ k) ↔ (4 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk' : k ≤ 8) :
    (3 ≤ k) ↔ (4 ≤ k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk' : k ≤ 8) :
    (3 ≤ k) ↔ (4 ≤ k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (4 ≤ k))) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (4 ≤ k))) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (4 ≤ k))) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (4 ≤ k))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (4 ≤ k))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (4 ≤ k))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (4 ≤ k))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (4 ≤ k))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (4 ≤ k))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (4 ≤ k))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (4 ≤ k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (4 ≤ k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (4 ≤ k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (4 ≤ k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (4 ≤ k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (4 ≤ k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (4 ≤ k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber < k + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber < k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber < k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber < k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber < k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber < k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber < k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber < k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber < k + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber < k + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber < k + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber < k + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber < k + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber < k + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber < k + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (k ≤ 8) ∧ (¬(J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (k ≤ 8) ∧ (¬(J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (k ≤ 8) ∧ (¬(J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (k ≤ 8) ∧ (¬(J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (k ≤ 8) ∧ (¬(J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (k ≤ 8) ∧ (¬(J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (k ≤ 8) ∧ (¬(J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (k ≤ 8) ∧ (¬(J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (k ≤ 8) ∧ (¬(J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (k ≤ 8) ∧ (¬(J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((J(2 * k, k).chromaticNumber > k + 1) ↔ (J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((J(2 * k, k).chromaticNumber > k + 1) ↔ (J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((J(2 * k, k).chromaticNumber > k + 1) ↔ (J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((J(2 * k, k).chromaticNumber > k + 1) ↔ (J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((J(2 * k, k).chromaticNumber > k + 1) ↔ (J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((J(2 * k, k).chromaticNumber > k + 1) ↔ (J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 3) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (k ≥ 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (k ≥ 3) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (k ≥ 3) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (k ≥ 3) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (k ≥ 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (k ≥ 3) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (k ≥ 3) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (k ≥ 3) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) ↔
    (∀ (k : ℕ) (hk : k ≥ 3) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) ↔
    (∀ (k : ℕ) (hk : k ≥ 3) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) ↔
    (∀ (k : ℕ) (hk : k ≥ 3) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) ↔
    (∀ (k : ℕ) (hk : k ≥ 3) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk' : k ≤ 8) (hk : 3 ≤ k), J(2 * k, k).chromaticNumber > k + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) ↔
    (∀ (k : ℕ) (hk' : k ≤ 8) (hk : 3 ≤ k), J(2 * k, k).chromaticNumber > k + 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) ↔
    (∀ (k : ℕ) (hk' : k ≤ 8) (hk : 3 ≤ k), J(2 * k, k).chromaticNumber > k + 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) ↔
    (∀ (k : ℕ) (hk' : k ≤ 8) (hk : 3 ≤ k), J(2 * k, k).chromaticNumber > k + 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) ↔
    (∀ (k : ℕ) (hk' : k ≤ 8) (hk : 3 ≤ k), J(2 * k, k).chromaticNumber > k + 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk₀ : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) ↔
    (∀ (k : ℕ) (hk₀ : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) ↔
    (∀ (k : ℕ) (hk₀ : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) ↔
    (∀ (k : ℕ) (hk₀ : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) ↔
    (∀ (k : ℕ) (hk₀ : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : ¬(k < 3)) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (¬(k < 3)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (¬(k < 3)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (¬(k < 3)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (¬(k < 3)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (¬(k < 3)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (¬(k < 3)) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (¬(k < 3)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (¬(k < 3)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) ↔
    (∀ (k : ℕ) (hk : ¬(k < 3)) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) ↔
    (∀ (k : ℕ) (hk : ¬(k < 3)) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) ↔
    (∀ (k : ℕ) (hk : ¬(k < 3)) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) ↔
    (∀ (k : ℕ) (hk : ¬(k < 3)) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 < k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (2 < k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (2 < k) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (2 < k) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (2 < k) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (2 < k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (2 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (2 < k) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (2 < k) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) ↔
    (∀ (k : ℕ) (hk : 2 < k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) ↔
    (∀ (k : ℕ) (hk : 2 < k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) ↔
    (∀ (k : ℕ) (hk : 2 < k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) ↔
    (∀ (k : ℕ) (hk : 2 < k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 3) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber ≥ k + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : k ≥ 3) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber ≥ k + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : k ≥ 3) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber ≥ k + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : k ≥ 3) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber ≥ k + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : k ≥ 3) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber ≥ k + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : k ≥ 3) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber ≥ k + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : k ≥ 3) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber ≥ k + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : k ≥ 3) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber ≥ k + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((J(2 * k, k).chromaticNumber > k + 1) ↔ (J(2 * k, k).chromaticNumber ≥ k + 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((J(2 * k, k).chromaticNumber > k + 1) ↔ (J(2 * k, k).chromaticNumber ≥ k + 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((J(2 * k, k).chromaticNumber > k + 1) ↔ (J(2 * k, k).chromaticNumber ≥ k + 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((J(2 * k, k).chromaticNumber > k + 1) ↔ (J(2 * k, k).chromaticNumber ≥ k + 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((J(2 * k, k).chromaticNumber > k + 1) ↔ (J(2 * k, k).chromaticNumber ≥ k + 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((J(2 * k, k).chromaticNumber > k + 1) ↔ (J(2 * k, k).chromaticNumber ≥ k + 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k > 3) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : k > 3) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : k > 3) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : k > 3) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : k > 3) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : k > 3) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : k > 3) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : k > 3) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk' : k ≤ 8) :
    (3 ≤ k) ↔ (k > 3) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk' : k ≤ 8) :
    (3 ≤ k) ↔ (k > 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk' : k ≤ 8) :
    (3 ≤ k) ↔ (k > 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk' : k ≤ 8) :
    (3 ≤ k) ↔ (k > 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk' : k ≤ 8) :
    (3 ≤ k) ↔ (k > 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk' : k ≤ 8) :
    (3 ≤ k) ↔ (k > 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk' : k ≤ 8) :
    (3 ≤ k) ↔ (k > 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (k > 3))) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (k > 3))) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (k > 3))) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (k > 3))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (k > 3))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (k > 3))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (k > 3))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (k > 3))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (k > 3))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (k > 3))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (k > 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (k > 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (k > 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (k > 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (k > 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (k > 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (k > 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 4) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : k ≥ 4) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : k ≥ 4) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : k ≥ 4) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : k ≥ 4) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : k ≥ 4) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : k ≥ 4) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : k ≥ 4) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk' : k ≤ 8) :
    (3 ≤ k) ↔ (k ≥ 4) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk' : k ≤ 8) :
    (3 ≤ k) ↔ (k ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk' : k ≤ 8) :
    (3 ≤ k) ↔ (k ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk' : k ≤ 8) :
    (3 ≤ k) ↔ (k ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk' : k ≤ 8) :
    (3 ≤ k) ↔ (k ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk' : k ≤ 8) :
    (3 ≤ k) ↔ (k ≥ 4) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk' : k ≤ 8) :
    (3 ≤ k) ↔ (k ≥ 4) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (k ≥ 4))) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (k ≥ 4))) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (k ≥ 4))) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (k ≥ 4))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (k ≥ 4))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (k ≥ 4))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (k ≥ 4))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (k ≥ 4))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (k ≥ 4))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (k ≥ 4))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (k ≥ 4)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (k ≥ 4)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (k ≥ 4)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (k ≥ 4)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (k ≥ 4)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (k ≥ 4)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (k ≥ 4)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 3) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber < k + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 3) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber < k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 3) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber < k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 3) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber < k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 3) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber < k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 3) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber < k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 3) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber < k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 3) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber < k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : k ≥ 3) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber < k + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : k ≥ 3) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber < k + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : k ≥ 3) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber < k + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : k ≥ 3) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber < k + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : k ≥ 3) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber < k + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : k ≥ 3) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber < k + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : k ≥ 3) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber < k + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (k ≤ 8) ∧ (¬(J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (k ≤ 8) ∧ (¬(J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (k ≤ 8) ∧ (¬(J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (k ≤ 8) ∧ (¬(J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (k ≤ 8) ∧ (¬(J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (k ≤ 8) ∧ (¬(J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (k ≤ 8) ∧ (¬(J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (k ≤ 8) ∧ (¬(J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (k ≤ 8) ∧ (¬(J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (k ≤ 8) ∧ (¬(J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((J(2 * k, k).chromaticNumber > k + 1) ↔ (J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((J(2 * k, k).chromaticNumber > k + 1) ↔ (J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((J(2 * k, k).chromaticNumber > k + 1) ↔ (J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((J(2 * k, k).chromaticNumber > k + 1) ↔ (J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((J(2 * k, k).chromaticNumber > k + 1) ↔ (J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((J(2 * k, k).chromaticNumber > k + 1) ↔ (J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk' : k ≤ 8) :
    (3 ≤ k) ↔ (2 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk' : k ≤ 8) :
    (3 ≤ k) ↔ (2 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk' : k ≤ 8) :
    (3 ≤ k) ↔ (2 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk' : k ≤ 8) :
    (3 ≤ k) ↔ (2 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk' : k ≤ 8) :
    (3 ≤ k) ↔ (2 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk' : k ≤ 8) :
    (3 ≤ k) ↔ (2 ≤ k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk' : k ≤ 8) :
    (3 ≤ k) ↔ (2 ≤ k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (2 ≤ k))) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (2 ≤ k))) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (2 ≤ k))) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (2 ≤ k))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (2 ≤ k))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (2 ≤ k))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (2 ≤ k))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (2 ≤ k))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (2 ≤ k))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k ≤ 8) ∧ (¬((3 ≤ k) ↔ (2 ≤ k))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (2 ≤ k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (2 ≤ k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (2 ≤ k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (2 ≤ k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (2 ≤ k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (2 ≤ k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (2 ≤ k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 < k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber ≥ k + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 2 < k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber ≥ k + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 2 < k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber ≥ k + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 2 < k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber ≥ k + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 2 < k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber ≥ k + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 2 < k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber ≥ k + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 2 < k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber ≥ k + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 2 < k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber ≥ k + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((J(2 * k, k).chromaticNumber > k + 1) ↔ (J(2 * k, k).chromaticNumber ≥ k + 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((J(2 * k, k).chromaticNumber > k + 1) ↔ (J(2 * k, k).chromaticNumber ≥ k + 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((J(2 * k, k).chromaticNumber > k + 1) ↔ (J(2 * k, k).chromaticNumber ≥ k + 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((J(2 * k, k).chromaticNumber > k + 1) ↔ (J(2 * k, k).chromaticNumber ≥ k + 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((J(2 * k, k).chromaticNumber > k + 1) ↔ (J(2 * k, k).chromaticNumber ≥ k + 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((J(2 * k, k).chromaticNumber > k + 1) ↔ (J(2 * k, k).chromaticNumber ≥ k + 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 < k) (hk' : k < 8), J(2 * k, k).chromaticNumber > k + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 2 < k) (hk' : k < 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 2 < k) (hk' : k < 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 2 < k) (hk' : k < 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 2 < k) (hk' : k < 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 2 < k) (hk' : k < 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 2 < k) (hk' : k < 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 2 < k) (hk' : k < 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 3 ≤ k) :
    (k ≤ 8) ↔ (k < 8) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 3 ≤ k) :
    (k ≤ 8) ↔ (k < 8) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 3 ≤ k) :
    (k ≤ 8) ↔ (k < 8) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 3 ≤ k) :
    (k ≤ 8) ↔ (k < 8) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 3 ≤ k) :
    (k ≤ 8) ↔ (k < 8) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 3 ≤ k) :
    (k ≤ 8) ↔ (k < 8) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 3 ≤ k) :
    (k ≤ 8) ↔ (k < 8) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((k ≤ 8) ↔ (k < 8))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((k ≤ 8) ↔ (k < 8))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((k ≤ 8) ↔ (k < 8))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((k ≤ 8) ↔ (k < 8))) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((k ≤ 8) ↔ (k < 8))) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((k ≤ 8) ↔ (k < 8))) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((k ≤ 8) ↔ (k < 8))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((k ≤ 8) ↔ (k < 8))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((k ≤ 8) ↔ (k < 8))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((k ≤ 8) ↔ (k < 8))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 8) ↔ (k < 8)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 8) ↔ (k < 8)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 8) ↔ (k < 8)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 8) ↔ (k < 8)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 8) ↔ (k < 8)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 8) ↔ (k < 8)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 8) ↔ (k < 8)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 8) ↔ (k < 8)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 8) ↔ (k < 8)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 < k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber < k + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 < k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber < k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 < k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber < k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 < k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber < k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 < k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber < k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 < k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber < k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 < k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber < k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 < k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber < k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 2 < k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber < k + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 2 < k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber < k + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 2 < k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber < k + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 2 < k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber < k + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 2 < k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber < k + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 2 < k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber < k + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 2 < k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber < k + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (k ≤ 8) ∧ (¬(J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (k ≤ 8) ∧ (¬(J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (k ≤ 8) ∧ (¬(J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (k ≤ 8) ∧ (¬(J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (k ≤ 8) ∧ (¬(J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (k ≤ 8) ∧ (¬(J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (k ≤ 8) ∧ (¬(J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (k ≤ 8) ∧ (¬(J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (k ≤ 8) ∧ (¬(J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (k ≤ 8) ∧ (¬(J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((J(2 * k, k).chromaticNumber > k + 1) ↔ (J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((J(2 * k, k).chromaticNumber > k + 1) ↔ (J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((J(2 * k, k).chromaticNumber > k + 1) ↔ (J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((J(2 * k, k).chromaticNumber > k + 1) ↔ (J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((J(2 * k, k).chromaticNumber > k + 1) ↔ (J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((J(2 * k, k).chromaticNumber > k + 1) ↔ (J(2 * k, k).chromaticNumber < k + 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k), J(2 * k, k).chromaticNumber > k + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), J(2 * k, k).chromaticNumber > k + 1) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8), J(2 * k, k).chromaticNumber > k + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 3 ≤ k) :
    (k ≤ 8) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 3 ≤ k) :
    (k ≤ 8) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 3 ≤ k) :
    (k ≤ 8) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 3 ≤ k) :
    (k ≤ 8) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 3 ≤ k) :
    (k ≤ 8) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 3 ≤ k) :
    (k ≤ 8) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 3 ≤ k) :
    (k ≤ 8) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((k ≤ 8) ↔ (True))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((k ≤ 8) ↔ (True))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((k ≤ 8) ↔ (True))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((k ≤ 8) ↔ (True))) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((k ≤ 8) ↔ (True))) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((k ≤ 8) ↔ (True))) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((k ≤ 8) ↔ (True))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((k ≤ 8) ↔ (True))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((k ≤ 8) ↔ (True))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((k ≤ 8) ↔ (True))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 8) ↔ (True)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 8) ↔ (True)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 8) ↔ (True)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 8) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 8) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 8) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 8) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 8) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 8) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
