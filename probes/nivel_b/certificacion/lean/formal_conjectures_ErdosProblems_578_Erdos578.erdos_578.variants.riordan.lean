import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Hypercube
/-!
# Erdős Problem 578

*References:*
- [erdosproblems.com/578](https://www.erdosproblems.com/578)
- [Ri00] Riordan, Oliver, *Spanning subgraphs of random graphs*.
  Combin. Probab. Comput. (2000), 125-148. [DOI](https://doi.org/10.1017/S0963548399004150)
-/

section

open Filter SimpleGraph

namespace Erdos578

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : unitInterval) (hp : (1 : ℝ) / 4 ≤ p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 ≤ p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) →
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 ≤ p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) →
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 ≤ p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) →
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 ≤ p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) →
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 ≤ p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) →
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 ≤ p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) →
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 ≤ p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) →
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p : unitInterval)  :
    ((1 : ℝ) / 4 < p) ↔ ((1 : ℝ) / 4 ≤ p) := by
  omega

set_option maxHeartbeats 200000 in
example (p : unitInterval)  :
    ((1 : ℝ) / 4 < p) ↔ ((1 : ℝ) / 4 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p : unitInterval)  :
    ((1 : ℝ) / 4 < p) ↔ ((1 : ℝ) / 4 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p : unitInterval)  :
    ((1 : ℝ) / 4 < p) ↔ ((1 : ℝ) / 4 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p : unitInterval)  :
    ((1 : ℝ) / 4 < p) ↔ ((1 : ℝ) / 4 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p : unitInterval)  :
    ((1 : ℝ) / 4 < p) ↔ ((1 : ℝ) / 4 ≤ p) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p : unitInterval)  :
    ((1 : ℝ) / 4 < p) ↔ ((1 : ℝ) / 4 ≤ p) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : unitInterval) (hp : (1 : ℝ) / 5 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 5 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) →
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 5 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) →
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 5 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) →
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 5 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) →
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 5 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) →
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 5 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) →
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 5 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) →
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) →
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 5 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) →
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 5 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) →
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 5 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) →
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 5 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) →
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 5 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) →
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 5 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) →
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 5 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p : unitInterval)  :
    ((1 : ℝ) / 4 < p) ↔ ((1 : ℝ) / 5 < p) := by
  omega

set_option maxHeartbeats 200000 in
example (p : unitInterval)  :
    ((1 : ℝ) / 4 < p) ↔ ((1 : ℝ) / 5 < p) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p : unitInterval)  :
    ((1 : ℝ) / 4 < p) ↔ ((1 : ℝ) / 5 < p) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p : unitInterval)  :
    ((1 : ℝ) / 4 < p) ↔ ((1 : ℝ) / 5 < p) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p : unitInterval)  :
    ((1 : ℝ) / 4 < p) ↔ ((1 : ℝ) / 5 < p) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p : unitInterval)  :
    ((1 : ℝ) / 4 < p) ↔ ((1 : ℝ) / 5 < p) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p : unitInterval)  :
    ((1 : ℝ) / 4 < p) ↔ ((1 : ℝ) / 5 < p) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : unitInterval) (hp : p > (1 : ℝ) / 4), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)

set_option maxHeartbeats 200000 in
example (p : unitInterval) :
    ((1 : ℝ) / 4 < p) ↔ (p > (1 : ℝ) / 4) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (p : unitInterval) :
    ((1 : ℝ) / 4 < p) ↔ (p > (1 : ℝ) / 4) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (p : unitInterval) :
    ((1 : ℝ) / 4 < p) ↔ (p > (1 : ℝ) / 4) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (p : unitInterval) :
    ((1 : ℝ) / 4 < p) ↔ (p > (1 : ℝ) / 4) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (p : unitInterval) :
    ((1 : ℝ) / 4 < p) ↔ (p > (1 : ℝ) / 4) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (p : unitInterval) :
    ((1 : ℝ) / 4 < p) ↔ (p > (1 : ℝ) / 4) := by
  omega

set_option maxHeartbeats 200000 in
example (p : unitInterval) :
    ((1 : ℝ) / 4 < p) ↔ (p > (1 : ℝ) / 4) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (p : unitInterval) :
    ((1 : ℝ) / 4 < p) ↔ (p > (1 : ℝ) / 4) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) ↔
    (∀ (p : unitInterval) (hp : p > (1 : ℝ) / 4), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) ↔
    (∀ (p : unitInterval) (hp : p > (1 : ℝ) / 4), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) ↔
    (∀ (p : unitInterval) (hp : p > (1 : ℝ) / 4), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) ↔
    (∀ (p : unitInterval) (hp : p > (1 : ℝ) / 4), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : unitInterval) (hp₀ : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) ↔
    (∀ (p : unitInterval) (hp₀ : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) ↔
    (∀ (p : unitInterval) (hp₀ : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) ↔
    (∀ (p : unitInterval) (hp₀ : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) ↔
    (∀ (p : unitInterval) (hp₀ : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : unitInterval) (hp : p ≥ (1 : ℝ) / 4), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : p ≥ (1 : ℝ) / 4), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) →
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : p ≥ (1 : ℝ) / 4), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) →
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : p ≥ (1 : ℝ) / 4), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) →
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : p ≥ (1 : ℝ) / 4), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) →
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : p ≥ (1 : ℝ) / 4), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) →
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : p ≥ (1 : ℝ) / 4), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) →
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : p ≥ (1 : ℝ) / 4), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) →
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p : unitInterval)  :
    ((1 : ℝ) / 4 < p) ↔ (p ≥ (1 : ℝ) / 4) := by
  omega

set_option maxHeartbeats 200000 in
example (p : unitInterval)  :
    ((1 : ℝ) / 4 < p) ↔ (p ≥ (1 : ℝ) / 4) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p : unitInterval)  :
    ((1 : ℝ) / 4 < p) ↔ (p ≥ (1 : ℝ) / 4) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p : unitInterval)  :
    ((1 : ℝ) / 4 < p) ↔ (p ≥ (1 : ℝ) / 4) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p : unitInterval)  :
    ((1 : ℝ) / 4 < p) ↔ (p ≥ (1 : ℝ) / 4) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p : unitInterval)  :
    ((1 : ℝ) / 4 < p) ↔ (p ≥ (1 : ℝ) / 4) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p : unitInterval)  :
    ((1 : ℝ) / 4 < p) ↔ (p ≥ (1 : ℝ) / 4) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : unitInterval) (hp : p > (1 : ℝ) / 5), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : p > (1 : ℝ) / 5), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) →
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : p > (1 : ℝ) / 5), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) →
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : p > (1 : ℝ) / 5), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) →
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : p > (1 : ℝ) / 5), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) →
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : p > (1 : ℝ) / 5), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) →
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : p > (1 : ℝ) / 5), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) →
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : p > (1 : ℝ) / 5), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) →
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) →
    (∀ (p : unitInterval) (hp : p > (1 : ℝ) / 5), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) →
    (∀ (p : unitInterval) (hp : p > (1 : ℝ) / 5), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) →
    (∀ (p : unitInterval) (hp : p > (1 : ℝ) / 5), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) →
    (∀ (p : unitInterval) (hp : p > (1 : ℝ) / 5), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) →
    (∀ (p : unitInterval) (hp : p > (1 : ℝ) / 5), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) →
    (∀ (p : unitInterval) (hp : p > (1 : ℝ) / 5), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : unitInterval) (hp : (1 : ℝ) / 4 < p), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) →
    (∀ (p : unitInterval) (hp : p > (1 : ℝ) / 5), Tendsto (fun d : ℕ =>
      binomialRandom (Fin d → Bool) p {G | (hypercube d).IsContained G})
      atTop (nhds 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p : unitInterval)  :
    ((1 : ℝ) / 4 < p) ↔ (p > (1 : ℝ) / 5) := by
  omega

set_option maxHeartbeats 200000 in
example (p : unitInterval)  :
    ((1 : ℝ) / 4 < p) ↔ (p > (1 : ℝ) / 5) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p : unitInterval)  :
    ((1 : ℝ) / 4 < p) ↔ (p > (1 : ℝ) / 5) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p : unitInterval)  :
    ((1 : ℝ) / 4 < p) ↔ (p > (1 : ℝ) / 5) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p : unitInterval)  :
    ((1 : ℝ) / 4 < p) ↔ (p > (1 : ℝ) / 5) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p : unitInterval)  :
    ((1 : ℝ) / 4 < p) ↔ (p > (1 : ℝ) / 5) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p : unitInterval)  :
    ((1 : ℝ) / 4 < p) ↔ (p > (1 : ℝ) / 5) := by
  plausible

set_option maxHeartbeats 200000 in
example (p : unitInterval) (hp : (1 : ℝ) / 4 < p) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (p : unitInterval) (hp : (1 : ℝ) / 4 < p) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (p : unitInterval) (hp : (1 : ℝ) / 4 < p) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (p : unitInterval) (hp : (1 : ℝ) / 4 < p) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (p : unitInterval) (hp : (1 : ℝ) / 4 < p) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
