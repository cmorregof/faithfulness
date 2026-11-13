import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Geometry.Metric
/-!
# Erdős Problem 1089

*References:*
- [erdosproblems.com/1089](https://www.erdosproblems.com/1089)
- [Er75f] Erdős, Paul, *On some problems of elementary and combinatorial geometry*. Ann. Mat. Pura
  Appl. (4) (1975), 99-108.
- [BBS83] Bannai, Eiichi and Bannai, Etsuko and Stanton, Dennis, *An upper bound for the
  cardinality of an $s$-distance subset in real Euclidean space. II*. Combinatorica (1983),
  147-152.
-/

section

open Filter
open scoped Topology

namespace Erdos1089

/-- `g d n` is the least `m` such that every `m` points in `ℝ^d` determine at least `n` distinct
distances, i.e. the least `m` with `n ≤ minimalDistinctDistances (EuclideanSpace ℝ (Fin d)) m`. -/
noncomputable def g (d n : ℕ) : ℕ :=
  sInf {m : ℕ | n ≤ minimalDistinctDistances (EuclideanSpace ℝ (Fin d)) m}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 < n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) →
    (∀ (n : ℕ) (hn : 2 < n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) →
    (∀ (n : ℕ) (hn : 2 < n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) →
    (∀ (n : ℕ) (hn : 2 < n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) →
    (∀ (n : ℕ) (hn : 2 < n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) →
    (∀ (n : ℕ) (hn : 2 < n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) →
    (∀ (n : ℕ) (hn : 2 < n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) →
    (∀ (n : ℕ) (hn : 2 < n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
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
  ∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
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
  ∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 2), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))

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
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) ↔
    (∀ (n : ℕ) (hn : n ≥ 2), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) ↔
    (∀ (n : ℕ) (hn : n ≥ 2), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) ↔
    (∀ (n : ℕ) (hn : n ≥ 2), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) ↔
    (∀ (n : ℕ) (hn : n ≥ 2), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), (∀ d₁, 1 ≤ d₁ → (d₁ + 1).choose (n - 1) + 1 ≤ g d₁ n ∧ g d₁ n ≤ (d₁ + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d₁ : ℕ => (g d₁ n : ℝ) / (d₁ : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) ↔ ((∀ d₁, 1 ≤ d₁ → (d₁ + 1).choose (n - 1) + 1 ≤ g d₁ n ∧ g d₁ n ≤ (d₁ + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d₁ : ℕ => (g d₁ n : ℝ) / (d₁ : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) ↔ ((∀ d₁, 1 ≤ d₁ → (d₁ + 1).choose (n - 1) + 1 ≤ g d₁ n ∧ g d₁ n ≤ (d₁ + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d₁ : ℕ => (g d₁ n : ℝ) / (d₁ : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) ↔ ((∀ d₁, 1 ≤ d₁ → (d₁ + 1).choose (n - 1) + 1 ≤ g d₁ n ∧ g d₁ n ≤ (d₁ + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d₁ : ℕ => (g d₁ n : ℝ) / (d₁ : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) ↔ ((∀ d₁, 1 ≤ d₁ → (d₁ + 1).choose (n - 1) + 1 ≤ g d₁ n ∧ g d₁ n ≤ (d₁ + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d₁ : ℕ => (g d₁ n : ℝ) / (d₁ : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) ↔ ((∀ d₁, 1 ≤ d₁ → (d₁ + 1).choose (n - 1) + 1 ≤ g d₁ n ∧ g d₁ n ≤ (d₁ + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d₁ : ℕ => (g d₁ n : ℝ) / (d₁ : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) ↔ ((∀ d₁, 1 ≤ d₁ → (d₁ + 1).choose (n - 1) + 1 ≤ g d₁ n ∧ g d₁ n ≤ (d₁ + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d₁ : ℕ => (g d₁ n : ℝ) / (d₁ : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) ↔ ((∀ d₁, 1 ≤ d₁ → (d₁ + 1).choose (n - 1) + 1 ≤ g d₁ n ∧ g d₁ n ≤ (d₁ + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d₁ : ℕ => (g d₁ n : ℝ) / (d₁ : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) ↔ ((∀ d₁, 1 ≤ d₁ → (d₁ + 1).choose (n - 1) + 1 ≤ g d₁ n ∧ g d₁ n ≤ (d₁ + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d₁ : ℕ => (g d₁ n : ℝ) / (d₁ : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) ↔
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d₁, 1 ≤ d₁ → (d₁ + 1).choose (n - 1) + 1 ≤ g d₁ n ∧ g d₁ n ≤ (d₁ + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d₁ : ℕ => (g d₁ n : ℝ) / (d₁ : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) ↔
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d₁, 1 ≤ d₁ → (d₁ + 1).choose (n - 1) + 1 ≤ g d₁ n ∧ g d₁ n ≤ (d₁ + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d₁ : ℕ => (g d₁ n : ℝ) / (d₁ : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) ↔
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d₁, 1 ≤ d₁ → (d₁ + 1).choose (n - 1) + 1 ≤ g d₁ n ∧ g d₁ n ≤ (d₁ + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d₁ : ℕ => (g d₁ n : ℝ) / (d₁ : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) ↔
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d₁, 1 ≤ d₁ → (d₁ + 1).choose (n - 1) + 1 ≤ g d₁ n ∧ g d₁ n ≤ (d₁ + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d₁ : ℕ => (g d₁ n : ℝ) / (d₁ : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn₀ : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) ↔
    (∀ (n : ℕ) (hn₀ : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) ↔
    (∀ (n : ℕ) (hn₀ : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) ↔
    (∀ (n : ℕ) (hn₀ : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) ↔
    (∀ (n : ℕ) (hn₀ : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : ¬(n < 2)), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))

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
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) ↔
    (∀ (n : ℕ) (hn : ¬(n < 2)), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) ↔
    (∀ (n : ℕ) (hn : ¬(n < 2)), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) ↔
    (∀ (n : ℕ) (hn : ¬(n < 2)), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) ↔
    (∀ (n : ℕ) (hn : ¬(n < 2)), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))

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
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) ↔
    (∀ (n : ℕ) (hn : 1 < n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) ↔
    (∀ (n : ℕ) (hn : 1 < n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) ↔
    (∀ (n : ℕ) (hn : 1 < n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) ↔
    (∀ (n : ℕ) (hn : 1 < n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 2), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) →
    (∀ (n : ℕ) (hn : n > 2), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) →
    (∀ (n : ℕ) (hn : n > 2), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) →
    (∀ (n : ℕ) (hn : n > 2), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) →
    (∀ (n : ℕ) (hn : n > 2), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) →
    (∀ (n : ℕ) (hn : n > 2), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) →
    (∀ (n : ℕ) (hn : n > 2), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) →
    (∀ (n : ℕ) (hn : n > 2), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
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
  ∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 3), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) →
    (∀ (n : ℕ) (hn : n ≥ 3), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) →
    (∀ (n : ℕ) (hn : n ≥ 3), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) →
    (∀ (n : ℕ) (hn : n ≥ 3), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) →
    (∀ (n : ℕ) (hn : n ≥ 3), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) →
    (∀ (n : ℕ) (hn : n ≥ 3), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) →
    (∀ (n : ℕ) (hn : n ≥ 3), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) →
    (∀ (n : ℕ) (hn : n ≥ 3), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
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
  ∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) →
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) →
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) →
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) →
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) →
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) →
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) →
    (∀ (n : ℕ) (hn : 2 ≤ n), (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial))) := by
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
