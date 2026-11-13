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

/-- Johnson's upper bound on the maximum size `A(n, d, w)` of a `n`-dimensional binary code of
distance `d` and weight `w` is as follows:
* If `d > 2 * w`, then `A(n, d, w) = 1`.
* If `d ≤ 2 * w`, then `A(n, d, w) ≤ ⌊n / w * A(n - 1, d, w - 1)⌋`. -/
def johnsonBound : ℕ → ℕ → ℕ → ℕ
  | 0, _d, _w => 1
  | _n, _d, 0 => 1
  | n + 1, d, w + 1 => if 2 * (w + 1) < d then 1 else (n + 1) * johnsonBound n d w / (w + 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber

set_option maxHeartbeats 200000 in
example :
    (∀ (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example  (hk' : k ≤ 300) (hk_odd : Odd k) :
    (3 ≤ k) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example  (hk' : k ≤ 300) (hk_odd : Odd k) :
    (3 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example  (hk' : k ≤ 300) (hk_odd : Odd k) :
    (3 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example  (hk' : k ≤ 300) (hk_odd : Odd k) :
    (3 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example  (hk' : k ≤ 300) (hk_odd : Odd k) :
    (3 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example  (hk' : k ≤ 300) (hk_odd : Odd k) :
    (3 ≤ k) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example  (hk' : k ≤ 300) (hk_odd : Odd k) :
    (3 ≤ k) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : (k ≤ 300) ∧ (Odd k) ∧ (¬((3 ≤ k) ↔ (True))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (k ≤ 300) ∧ (Odd k) ∧ (¬((3 ≤ k) ↔ (True))) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((3 ≤ k) ↔ (True)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((3 ≤ k) ↔ (True)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 ≤ J(2 * k, k).chromaticNumber

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 ≤ J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 ≤ J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 ≤ J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 ≤ J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 ≤ J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 ≤ J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 ≤ J(2 * k, k).chromaticNumber) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ¬((k + 1 < J(2 * k, k).chromaticNumber) ↔ (k + 1 ≤ J(2 * k, k).chromaticNumber)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((k + 1 < J(2 * k, k).chromaticNumber) ↔ (k + 1 ≤ J(2 * k, k).chromaticNumber)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hk : 3 < k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 < k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 < k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 < k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 < k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 < k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 < k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 < k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example  (hk' : k ≤ 300) (hk_odd : Odd k) :
    (3 ≤ k) ↔ (3 < k) := by
  omega

set_option maxHeartbeats 200000 in
example  (hk' : k ≤ 300) (hk_odd : Odd k) :
    (3 ≤ k) ↔ (3 < k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example  (hk' : k ≤ 300) (hk_odd : Odd k) :
    (3 ≤ k) ↔ (3 < k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example  (hk' : k ≤ 300) (hk_odd : Odd k) :
    (3 ≤ k) ↔ (3 < k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example  (hk' : k ≤ 300) (hk_odd : Odd k) :
    (3 ≤ k) ↔ (3 < k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example  (hk' : k ≤ 300) (hk_odd : Odd k) :
    (3 ≤ k) ↔ (3 < k) := by
  simp_all

set_option maxHeartbeats 200000 in
example  (hk' : k ≤ 300) (hk_odd : Odd k) :
    (3 ≤ k) ↔ (3 < k) := by
  plausible

set_option maxHeartbeats 200000 in
example : (k ≤ 300) ∧ (Odd k) ∧ (¬((3 ≤ k) ↔ (3 < k))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (k ≤ 300) ∧ (Odd k) ∧ (¬((3 ≤ k) ↔ (3 < k))) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((3 ≤ k) ↔ (3 < k)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((3 ≤ k) ↔ (3 < k)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hk : 4 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : 4 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : 4 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : 4 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : 4 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : 4 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : 4 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : 4 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example  (hk' : k ≤ 300) (hk_odd : Odd k) :
    (3 ≤ k) ↔ (4 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example  (hk' : k ≤ 300) (hk_odd : Odd k) :
    (3 ≤ k) ↔ (4 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example  (hk' : k ≤ 300) (hk_odd : Odd k) :
    (3 ≤ k) ↔ (4 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example  (hk' : k ≤ 300) (hk_odd : Odd k) :
    (3 ≤ k) ↔ (4 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example  (hk' : k ≤ 300) (hk_odd : Odd k) :
    (3 ≤ k) ↔ (4 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example  (hk' : k ≤ 300) (hk_odd : Odd k) :
    (3 ≤ k) ↔ (4 ≤ k) := by
  simp_all

set_option maxHeartbeats 200000 in
example  (hk' : k ≤ 300) (hk_odd : Odd k) :
    (3 ≤ k) ↔ (4 ≤ k) := by
  plausible

set_option maxHeartbeats 200000 in
example : (k ≤ 300) ∧ (Odd k) ∧ (¬((3 ≤ k) ↔ (4 ≤ k))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (k ≤ 300) ∧ (Odd k) ∧ (¬((3 ≤ k) ↔ (4 ≤ k))) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((3 ≤ k) ↔ (4 ≤ k)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((3 ≤ k) ↔ (4 ≤ k)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 > J(2 * k, k).chromaticNumber

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 > J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 > J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 > J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 > J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 > J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 > J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 > J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 > J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 > J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 > J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 > J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 > J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 > J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 > J(2 * k, k).chromaticNumber) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (3 ≤ k) ∧ (k ≤ 300) ∧ (Odd k) ∧ (¬(k + 1 > J(2 * k, k).chromaticNumber)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (3 ≤ k) ∧ (k ≤ 300) ∧ (Odd k) ∧ (¬(k + 1 > J(2 * k, k).chromaticNumber)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((k + 1 < J(2 * k, k).chromaticNumber) ↔ (k + 1 > J(2 * k, k).chromaticNumber)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((k + 1 < J(2 * k, k).chromaticNumber) ↔ (k + 1 > J(2 * k, k).chromaticNumber)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hk : k ≥ 3) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber

set_option maxHeartbeats 200000 in
example  :
    (3 ≤ k) ↔ (k ≥ 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example  :
    (3 ≤ k) ↔ (k ≥ 3) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example  :
    (3 ≤ k) ↔ (k ≥ 3) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example  :
    (3 ≤ k) ↔ (k ≥ 3) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example  :
    (3 ≤ k) ↔ (k ≥ 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example  :
    (3 ≤ k) ↔ (k ≥ 3) := by
  omega

set_option maxHeartbeats 200000 in
example  :
    (3 ≤ k) ↔ (k ≥ 3) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example  :
    (3 ≤ k) ↔ (k ≥ 3) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) ↔
    (∀ (hk : k ≥ 3) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) ↔
    (∀ (hk : k ≥ 3) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) ↔
    (∀ (hk : k ≥ 3) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) ↔
    (∀ (hk : k ≥ 3) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hk' : k ≤ 300) (hk : 3 ≤ k) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) ↔
    (∀ (hk' : k ≤ 300) (hk : 3 ≤ k) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) ↔
    (∀ (hk' : k ≤ 300) (hk : 3 ≤ k) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) ↔
    (∀ (hk' : k ≤ 300) (hk : 3 ≤ k) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) ↔
    (∀ (hk' : k ≤ 300) (hk : 3 ≤ k) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hk₀ : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) ↔
    (∀ (hk₀ : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) ↔
    (∀ (hk₀ : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) ↔
    (∀ (hk₀ : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) ↔
    (∀ (hk₀ : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hk : ¬(k < 3)) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber

set_option maxHeartbeats 200000 in
example  :
    (3 ≤ k) ↔ (¬(k < 3)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example  :
    (3 ≤ k) ↔ (¬(k < 3)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example  :
    (3 ≤ k) ↔ (¬(k < 3)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example  :
    (3 ≤ k) ↔ (¬(k < 3)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example  :
    (3 ≤ k) ↔ (¬(k < 3)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example  :
    (3 ≤ k) ↔ (¬(k < 3)) := by
  omega

set_option maxHeartbeats 200000 in
example  :
    (3 ≤ k) ↔ (¬(k < 3)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example  :
    (3 ≤ k) ↔ (¬(k < 3)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) ↔
    (∀ (hk : ¬(k < 3)) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) ↔
    (∀ (hk : ¬(k < 3)) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) ↔
    (∀ (hk : ¬(k < 3)) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) ↔
    (∀ (hk : ¬(k < 3)) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hk : k ≥ 3) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 ≤ J(2 * k, k).chromaticNumber

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : k ≥ 3) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 ≤ J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : k ≥ 3) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 ≤ J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : k ≥ 3) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 ≤ J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : k ≥ 3) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 ≤ J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : k ≥ 3) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 ≤ J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : k ≥ 3) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 ≤ J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : k ≥ 3) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 ≤ J(2 * k, k).chromaticNumber) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ¬((k + 1 < J(2 * k, k).chromaticNumber) ↔ (k + 1 ≤ J(2 * k, k).chromaticNumber)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((k + 1 < J(2 * k, k).chromaticNumber) ↔ (k + 1 ≤ J(2 * k, k).chromaticNumber)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hk : k > 3) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : k > 3) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : k > 3) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : k > 3) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : k > 3) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : k > 3) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : k > 3) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : k > 3) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example  (hk' : k ≤ 300) (hk_odd : Odd k) :
    (3 ≤ k) ↔ (k > 3) := by
  omega

set_option maxHeartbeats 200000 in
example  (hk' : k ≤ 300) (hk_odd : Odd k) :
    (3 ≤ k) ↔ (k > 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example  (hk' : k ≤ 300) (hk_odd : Odd k) :
    (3 ≤ k) ↔ (k > 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example  (hk' : k ≤ 300) (hk_odd : Odd k) :
    (3 ≤ k) ↔ (k > 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example  (hk' : k ≤ 300) (hk_odd : Odd k) :
    (3 ≤ k) ↔ (k > 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example  (hk' : k ≤ 300) (hk_odd : Odd k) :
    (3 ≤ k) ↔ (k > 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example  (hk' : k ≤ 300) (hk_odd : Odd k) :
    (3 ≤ k) ↔ (k > 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : (k ≤ 300) ∧ (Odd k) ∧ (¬((3 ≤ k) ↔ (k > 3))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (k ≤ 300) ∧ (Odd k) ∧ (¬((3 ≤ k) ↔ (k > 3))) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((3 ≤ k) ↔ (k > 3)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((3 ≤ k) ↔ (k > 3)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hk : k ≥ 4) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : k ≥ 4) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : k ≥ 4) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : k ≥ 4) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : k ≥ 4) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : k ≥ 4) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : k ≥ 4) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : k ≥ 4) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example  (hk' : k ≤ 300) (hk_odd : Odd k) :
    (3 ≤ k) ↔ (k ≥ 4) := by
  omega

set_option maxHeartbeats 200000 in
example  (hk' : k ≤ 300) (hk_odd : Odd k) :
    (3 ≤ k) ↔ (k ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example  (hk' : k ≤ 300) (hk_odd : Odd k) :
    (3 ≤ k) ↔ (k ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example  (hk' : k ≤ 300) (hk_odd : Odd k) :
    (3 ≤ k) ↔ (k ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example  (hk' : k ≤ 300) (hk_odd : Odd k) :
    (3 ≤ k) ↔ (k ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example  (hk' : k ≤ 300) (hk_odd : Odd k) :
    (3 ≤ k) ↔ (k ≥ 4) := by
  simp_all

set_option maxHeartbeats 200000 in
example  (hk' : k ≤ 300) (hk_odd : Odd k) :
    (3 ≤ k) ↔ (k ≥ 4) := by
  plausible

set_option maxHeartbeats 200000 in
example : (k ≤ 300) ∧ (Odd k) ∧ (¬((3 ≤ k) ↔ (k ≥ 4))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (k ≤ 300) ∧ (Odd k) ∧ (¬((3 ≤ k) ↔ (k ≥ 4))) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((3 ≤ k) ↔ (k ≥ 4)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((3 ≤ k) ↔ (k ≥ 4)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hk : k ≥ 3) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 > J(2 * k, k).chromaticNumber

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : k ≥ 3) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 > J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : k ≥ 3) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 > J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : k ≥ 3) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 > J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : k ≥ 3) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 > J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : k ≥ 3) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 > J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : k ≥ 3) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 > J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : k ≥ 3) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 > J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : k ≥ 3) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 > J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : k ≥ 3) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 > J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : k ≥ 3) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 > J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : k ≥ 3) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 > J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : k ≥ 3) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 > J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : k ≥ 3) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 > J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : k ≥ 3) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 > J(2 * k, k).chromaticNumber) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (3 ≤ k) ∧ (k ≤ 300) ∧ (Odd k) ∧ (¬(k + 1 > J(2 * k, k).chromaticNumber)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (3 ≤ k) ∧ (k ≤ 300) ∧ (Odd k) ∧ (¬(k + 1 > J(2 * k, k).chromaticNumber)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((k + 1 < J(2 * k, k).chromaticNumber) ↔ (k + 1 > J(2 * k, k).chromaticNumber)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((k + 1 < J(2 * k, k).chromaticNumber) ↔ (k + 1 > J(2 * k, k).chromaticNumber)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (hk : 3 ≤ k) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (hk : 3 ≤ k) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) →
    (∀ (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k), k + 1 < J(2 * k, k).chromaticNumber) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example  (hk : 3 ≤ k) (hk_odd : Odd k) :
    (k ≤ 300) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example  (hk : 3 ≤ k) (hk_odd : Odd k) :
    (k ≤ 300) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example  (hk : 3 ≤ k) (hk_odd : Odd k) :
    (k ≤ 300) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example  (hk : 3 ≤ k) (hk_odd : Odd k) :
    (k ≤ 300) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example  (hk : 3 ≤ k) (hk_odd : Odd k) :
    (k ≤ 300) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example  (hk : 3 ≤ k) (hk_odd : Odd k) :
    (k ≤ 300) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example  (hk : 3 ≤ k) (hk_odd : Odd k) :
    (k ≤ 300) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : (3 ≤ k) ∧ (Odd k) ∧ (¬((k ≤ 300) ↔ (True))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (3 ≤ k) ∧ (Odd k) ∧ (¬((k ≤ 300) ↔ (True))) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((k ≤ 300) ↔ (True)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((k ≤ 300) ↔ (True)) :=
  by decide

set_option maxHeartbeats 200000 in
example  (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example  (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example  (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example  (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example  (hk : 3 ≤ k) (hk' : k ≤ 300) (hk_odd : Odd k) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
