import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 967

*References:*
- [erdosproblems.com/967](https://www.erdosproblems.com/967)
- [ErIn64] Erdős, P. and Ingham, A. E., *Arithmetical Tauberian theorems*. Acta Arith. (1964),
  341-356.
- [Yi25] Yip, F., *On a problem of Erdős and Ingham*. arXiv:2512.16528 (2025).
-/

section

open Filter

open scoped Topology

namespace Erdos967

/-- The summand $\frac{1}{n^{1+it}}$, for a natural number $n$ and $t\in\mathbb{R}$. -/
noncomputable def summand (t : ℝ) (n : ℕ) : ℂ := 1 / (n : ℂ) ^ (1 + t * Complex.I : ℂ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℕ → ℕ) (ha : StrictMono a) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) →
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) →
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) →
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) →
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) →
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) →
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) →
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a : ℕ → ℕ) (ha : StrictMono a) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))) :
    (1 < a 0) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (a : ℕ → ℕ) (ha : StrictMono a) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))) :
    (1 < a 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a : ℕ → ℕ) (ha : StrictMono a) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))) :
    (1 < a 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a : ℕ → ℕ) (ha : StrictMono a) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))) :
    (1 < a 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a : ℕ → ℕ) (ha : StrictMono a) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))) :
    (1 < a 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a : ℕ → ℕ) (ha : StrictMono a) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))) :
    (1 < a 0) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a : ℕ → ℕ) (ha : StrictMono a) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))) :
    (1 < a 0) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 ≤ a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 ≤ a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) →
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 ≤ a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) →
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 ≤ a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) →
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 ≤ a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) →
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 ≤ a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) →
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 ≤ a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) →
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 ≤ a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) →
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a : ℕ → ℕ) (ha : StrictMono a) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))) :
    (1 < a 0) ↔ (1 ≤ a 0) := by
  omega

set_option maxHeartbeats 200000 in
example (a : ℕ → ℕ) (ha : StrictMono a) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))) :
    (1 < a 0) ↔ (1 ≤ a 0) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a : ℕ → ℕ) (ha : StrictMono a) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))) :
    (1 < a 0) ↔ (1 ≤ a 0) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a : ℕ → ℕ) (ha : StrictMono a) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))) :
    (1 < a 0) ↔ (1 ≤ a 0) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a : ℕ → ℕ) (ha : StrictMono a) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))) :
    (1 < a 0) ↔ (1 ≤ a 0) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a : ℕ → ℕ) (ha : StrictMono a) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))) :
    (1 < a 0) ↔ (1 ≤ a 0) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a : ℕ → ℕ) (ha : StrictMono a) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))) :
    (1 < a 0) ↔ (1 ≤ a 0) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : a 0 > 1) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)

set_option maxHeartbeats 200000 in
example (a : ℕ → ℕ) :
    (1 < a 0) ↔ (a 0 > 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (a : ℕ → ℕ) :
    (1 < a 0) ↔ (a 0 > 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (a : ℕ → ℕ) :
    (1 < a 0) ↔ (a 0 > 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (a : ℕ → ℕ) :
    (1 < a 0) ↔ (a 0 > 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (a : ℕ → ℕ) :
    (1 < a 0) ↔ (a 0 > 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (a : ℕ → ℕ) :
    (1 < a 0) ↔ (a 0 > 1) := by
  omega

set_option maxHeartbeats 200000 in
example (a : ℕ → ℕ) :
    (1 < a 0) ↔ (a 0 > 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (a : ℕ → ℕ) :
    (1 < a 0) ↔ (a 0 > 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) ↔
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : a 0 > 1) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) ↔
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : a 0 > 1) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) ↔
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : a 0 > 1) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) ↔
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : a 0 > 1) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t₁ : ℝ, 1 + (∑' k, summand t₁ (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)

set_option maxHeartbeats 200000 in
example (a : ℕ → ℕ) :
    ((∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) ↔ ((∀ t₁ : ℝ, 1 + (∑' k, summand t₁ (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (a : ℕ → ℕ) :
    ((∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) ↔ ((∀ t₁ : ℝ, 1 + (∑' k, summand t₁ (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (a : ℕ → ℕ) :
    ((∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) ↔ ((∀ t₁ : ℝ, 1 + (∑' k, summand t₁ (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (a : ℕ → ℕ) :
    ((∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) ↔ ((∀ t₁ : ℝ, 1 + (∑' k, summand t₁ (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (a : ℕ → ℕ) :
    ((∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) ↔ ((∀ t₁ : ℝ, 1 + (∑' k, summand t₁ (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (a : ℕ → ℕ) :
    ((∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) ↔ ((∀ t₁ : ℝ, 1 + (∑' k, summand t₁ (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) := by
  omega

set_option maxHeartbeats 200000 in
example (a : ℕ → ℕ) :
    ((∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) ↔ ((∀ t₁ : ℝ, 1 + (∑' k, summand t₁ (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (a : ℕ → ℕ) :
    ((∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) ↔ ((∀ t₁ : ℝ, 1 + (∑' k, summand t₁ (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) ↔
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t₁ : ℝ, 1 + (∑' k, summand t₁ (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) ↔
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t₁ : ℝ, 1 + (∑' k, summand t₁ (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) ↔
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t₁ : ℝ, 1 + (∑' k, summand t₁ (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) ↔
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t₁ : ℝ, 1 + (∑' k, summand t₁ (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℕ → ℕ) (ha₀ : 1 < a 0) (ha : StrictMono a) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) ↔
    (∀ (a : ℕ → ℕ) (ha₀ : 1 < a 0) (ha : StrictMono a) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) ↔
    (∀ (a : ℕ → ℕ) (ha₀ : 1 < a 0) (ha : StrictMono a) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) ↔
    (∀ (a : ℕ → ℕ) (ha₀ : 1 < a 0) (ha : StrictMono a) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) ↔
    (∀ (a : ℕ → ℕ) (ha₀ : 1 < a 0) (ha : StrictMono a) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀' : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) ↔
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀' : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) ↔
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀' : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) ↔
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀' : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) ↔
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀' : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : a 0 ≥ 1) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : a 0 ≥ 1) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) →
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : a 0 ≥ 1) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) →
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : a 0 ≥ 1) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) →
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : a 0 ≥ 1) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) →
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : a 0 ≥ 1) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) →
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : a 0 ≥ 1) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) →
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : a 0 ≥ 1) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) →
    (∀ (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))), (∀ t : ℝ, 1 + (∑' k, summand t (a k)) ≠ 0) ↔
      ∀ f : ℝ → ℝ, Monotone f → (∀ x : ℝ, 0 ≤ f x) → (∀ x < 1, f x = 0) →
        (∀ x y : ℝ, BddAbove (f '' Set.Icc x y)) →
        Tendsto (fun x : ℝ => (f x + ∑' k, f (x / (a k : ℝ))) / x) atTop
          (𝓝 (1 + ∑' k, 1 / (a k : ℝ))) →
        Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a : ℕ → ℕ) (ha : StrictMono a) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))) :
    (1 < a 0) ↔ (a 0 ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example (a : ℕ → ℕ) (ha : StrictMono a) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))) :
    (1 < a 0) ↔ (a 0 ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a : ℕ → ℕ) (ha : StrictMono a) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))) :
    (1 < a 0) ↔ (a 0 ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a : ℕ → ℕ) (ha : StrictMono a) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))) :
    (1 < a 0) ↔ (a 0 ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a : ℕ → ℕ) (ha : StrictMono a) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))) :
    (1 < a 0) ↔ (a 0 ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a : ℕ → ℕ) (ha : StrictMono a) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))) :
    (1 < a 0) ↔ (a 0 ≥ 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a : ℕ → ℕ) (ha : StrictMono a) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))) :
    (1 < a 0) ↔ (a 0 ≥ 1) := by
  plausible

set_option maxHeartbeats 200000 in
example (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (a : ℕ → ℕ) (ha : StrictMono a) (ha₀ : 1 < a 0) (hsum : Summable (fun k : ℕ => 1 / (a k : ℝ))) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
