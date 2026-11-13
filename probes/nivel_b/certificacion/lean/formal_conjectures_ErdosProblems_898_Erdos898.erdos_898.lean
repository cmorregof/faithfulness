import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   notación `ℝ²` (scoped EuclideanGeometry, FCM.Geometry.2d)
/-!
# Erdős Problem 898

*References:*
- [erdosproblems.com/898](https://www.erdosproblems.com/898)
- [Er82e] Erdős, Paul, *Some of my favourite problems which recently have been solved*.
  (1982), 59--79.
- [Wikipedia](https://en.wikipedia.org/wiki/Erd%C5%91s%E2%80%93Mordell_inequality)
-/

section

open Affine EuclideanGeometry

namespace Erdos898

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C > 2 * (dist P M + dist P N + dist P L)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C > 2 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C > 2 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C > 2 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C > 2 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C > 2 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C > 2 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C > 2 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 3 * (dist P M + dist P N + dist P L)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 3 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 3 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 3 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 3 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 3 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 3 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 3 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 3 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 3 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 3 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 3 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 3 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 3 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 3 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≤ 2 * (dist P M + dist P N + dist P L)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≤ 2 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≤ 2 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≤ 2 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≤ 2 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≤ 2 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≤ 2 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≤ 2 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≤ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≤ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≤ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≤ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≤ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≤ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≤ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), 2 * (dist P M + dist P N + dist P L) ≤ dist P A + dist P B + dist P C

set_option maxHeartbeats 200000 in
example (A B C P L M N : ℝ²) :
    (dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) ↔ (2 * (dist P M + dist P N + dist P L) ≤ dist P A + dist P B + dist P C) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (A B C P L M N : ℝ²) :
    (dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) ↔ (2 * (dist P M + dist P N + dist P L) ≤ dist P A + dist P B + dist P C) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (A B C P L M N : ℝ²) :
    (dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) ↔ (2 * (dist P M + dist P N + dist P L) ≤ dist P A + dist P B + dist P C) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (A B C P L M N : ℝ²) :
    (dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) ↔ (2 * (dist P M + dist P N + dist P L) ≤ dist P A + dist P B + dist P C) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (A B C P L M N : ℝ²) :
    (dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) ↔ (2 * (dist P M + dist P N + dist P L) ≤ dist P A + dist P B + dist P C) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (A B C P L M N : ℝ²) :
    (dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) ↔ (2 * (dist P M + dist P N + dist P L) ≤ dist P A + dist P B + dist P C) := by
  omega

set_option maxHeartbeats 200000 in
example (A B C P L M N : ℝ²) :
    (dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) ↔ (2 * (dist P M + dist P N + dist P L) ≤ dist P A + dist P B + dist P C) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (A B C P L M N : ℝ²) :
    (dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) ↔ (2 * (dist P M + dist P N + dist P L) ≤ dist P A + dist P B + dist P C) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) ↔
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), 2 * (dist P M + dist P N + dist P L) ≤ dist P A + dist P B + dist P C) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) ↔
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), 2 * (dist P M + dist P N + dist P L) ≤ dist P A + dist P B + dist P C) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) ↔
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), 2 * (dist P M + dist P N + dist P L) ≤ dist P A + dist P B + dist P C) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) ↔
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), 2 * (dist P M + dist P N + dist P L) ≤ dist P A + dist P B + dist P C) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B C P L M N : ℝ²) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hABC : AffineIndependent ℝ ![A, B, C]) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) ↔
    (∀ (A B C P L M N : ℝ²) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hABC : AffineIndependent ℝ ![A, B, C]) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) ↔
    (∀ (A B C P L M N : ℝ²) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hABC : AffineIndependent ℝ ![A, B, C]) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) ↔
    (∀ (A B C P L M N : ℝ²) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hABC : AffineIndependent ℝ ![A, B, C]) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) ↔
    (∀ (A B C P L M N : ℝ²) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hABC : AffineIndependent ℝ ![A, B, C]) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B C P L M N : ℝ²) (hABC₀ : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) ↔
    (∀ (A B C P L M N : ℝ²) (hABC₀ : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) ↔
    (∀ (A B C P L M N : ℝ²) (hABC₀ : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) ↔
    (∀ (A B C P L M N : ℝ²) (hABC₀ : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) ↔
    (∀ (A B C P L M N : ℝ²) (hABC₀ : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), 2 * (dist P M + dist P N + dist P L) < dist P A + dist P B + dist P C

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), 2 * (dist P M + dist P N + dist P L) < dist P A + dist P B + dist P C) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), 2 * (dist P M + dist P N + dist P L) < dist P A + dist P B + dist P C) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), 2 * (dist P M + dist P N + dist P L) < dist P A + dist P B + dist P C) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), 2 * (dist P M + dist P N + dist P L) < dist P A + dist P B + dist P C) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), 2 * (dist P M + dist P N + dist P L) < dist P A + dist P B + dist P C) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), 2 * (dist P M + dist P N + dist P L) < dist P A + dist P B + dist P C) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), 2 * (dist P M + dist P N + dist P L) < dist P A + dist P B + dist P C) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), 3 * (dist P M + dist P N + dist P L) ≤ dist P A + dist P B + dist P C

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), 3 * (dist P M + dist P N + dist P L) ≤ dist P A + dist P B + dist P C) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), 3 * (dist P M + dist P N + dist P L) ≤ dist P A + dist P B + dist P C) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), 3 * (dist P M + dist P N + dist P L) ≤ dist P A + dist P B + dist P C) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), 3 * (dist P M + dist P N + dist P L) ≤ dist P A + dist P B + dist P C) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), 3 * (dist P M + dist P N + dist P L) ≤ dist P A + dist P B + dist P C) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), 3 * (dist P M + dist P N + dist P L) ≤ dist P A + dist P B + dist P C) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), 3 * (dist P M + dist P N + dist P L) ≤ dist P A + dist P B + dist P C) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), 3 * (dist P M + dist P N + dist P L) ≤ dist P A + dist P B + dist P C) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), 3 * (dist P M + dist P N + dist P L) ≤ dist P A + dist P B + dist P C) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), 3 * (dist P M + dist P N + dist P L) ≤ dist P A + dist P B + dist P C) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), 3 * (dist P M + dist P N + dist P L) ≤ dist P A + dist P B + dist P C) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), 3 * (dist P M + dist P N + dist P L) ≤ dist P A + dist P B + dist P C) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), 3 * (dist P M + dist P N + dist P L) ≤ dist P A + dist P B + dist P C) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), 3 * (dist P M + dist P N + dist P L) ≤ dist P A + dist P B + dist P C) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), 2 * (dist P M + dist P N + dist P L) ≥ dist P A + dist P B + dist P C

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), 2 * (dist P M + dist P N + dist P L) ≥ dist P A + dist P B + dist P C) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), 2 * (dist P M + dist P N + dist P L) ≥ dist P A + dist P B + dist P C) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), 2 * (dist P M + dist P N + dist P L) ≥ dist P A + dist P B + dist P C) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), 2 * (dist P M + dist P N + dist P L) ≥ dist P A + dist P B + dist P C) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), 2 * (dist P M + dist P N + dist P L) ≥ dist P A + dist P B + dist P C) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), 2 * (dist P M + dist P N + dist P L) ≥ dist P A + dist P B + dist P C) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), 2 * (dist P M + dist P N + dist P L) ≥ dist P A + dist P B + dist P C) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), 2 * (dist P M + dist P N + dist P L) ≥ dist P A + dist P B + dist P C) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), 2 * (dist P M + dist P N + dist P L) ≥ dist P A + dist P B + dist P C) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), 2 * (dist P M + dist P N + dist P L) ≥ dist P A + dist P B + dist P C) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), 2 * (dist P M + dist P N + dist P L) ≥ dist P A + dist P B + dist P C) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), 2 * (dist P M + dist P N + dist P L) ≥ dist P A + dist P B + dist P C) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), 2 * (dist P M + dist P N + dist P L) ≥ dist P A + dist P B + dist P C) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)) →
    (∀ (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction), 2 * (dist P M + dist P N + dist P L) ≥ dist P A + dist P B + dist P C) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C]) (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²))) (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction) (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction) (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
