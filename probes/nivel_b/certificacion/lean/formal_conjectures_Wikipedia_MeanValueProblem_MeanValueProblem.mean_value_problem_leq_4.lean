import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Mean value problem

*Reference:*
- [Wikipedia](https://en.wikipedia.org/wiki/Mean_value_problem)
- [The fundamental theorem of algebra and complexity theory](https://www.ams.org/journals/bull/1981-04-01/S0273-0979-1981-14858-8/)
by Steve Smale

Given a complex polynomial $p$ of degree $d ≥ 2$ and a complex number $z$
there is a critical point $c$ of $p$, such that $|p(z)-p(c)|/|z-c| ≤ K* |p'(z)|$ for $K=1$.

The conjecture has been proven for:
* `K = 4`
  [The fundamental theorem of algebra and complexity theory](https://www.ams.org/journals/bull/1981-04-01/S0273-0979-1981-14858-8/)
  by *Steve Smale*
* `K = (d-1)/d` at a point $z$ if the normalised polynomial $p(X + z) - p(z)$ has only real
  roots, or if all its nonzero roots have the same norm.
  [Critical points and values of complex polynomials](https://doi.org/10.1016/0885-064X(89)90019-8)
  by *David Tischler*
-/

section

namespace MeanValueProblem

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : Polynomial ℂ) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ)  :
    (2 ≤ p.degree) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ)  :
    (2 ≤ p.degree) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ)  :
    (2 ≤ p.degree) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ)  :
    (2 ≤ p.degree) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ)  :
    (2 ≤ p.degree) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ)  :
    (2 ≤ p.degree) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ)  :
    (2 ≤ p.degree) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ < 4 *‖p.derivative.eval z‖

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ < 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ < 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ < 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ < 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ < 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ < 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ < 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : Polynomial ℂ) (hp : 2 < p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 < p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 < p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 < p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 < p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 < p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 < p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 < p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ)  :
    (2 ≤ p.degree) ↔ (2 < p.degree) := by
  omega

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ)  :
    (2 ≤ p.degree) ↔ (2 < p.degree) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ)  :
    (2 ≤ p.degree) ↔ (2 < p.degree) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ)  :
    (2 ≤ p.degree) ↔ (2 < p.degree) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ)  :
    (2 ≤ p.degree) ↔ (2 < p.degree) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ)  :
    (2 ≤ p.degree) ↔ (2 < p.degree) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ)  :
    (2 ≤ p.degree) ↔ (2 < p.degree) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : Polynomial ℂ) (hp : 3 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 3 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 3 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 3 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 3 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 3 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 3 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 3 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ)  :
    (2 ≤ p.degree) ↔ (3 ≤ p.degree) := by
  omega

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ)  :
    (2 ≤ p.degree) ↔ (3 ≤ p.degree) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ)  :
    (2 ≤ p.degree) ↔ (3 ≤ p.degree) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ)  :
    (2 ≤ p.degree) ↔ (3 ≤ p.degree) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ)  :
    (2 ≤ p.degree) ↔ (3 ≤ p.degree) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ)  :
    (2 ≤ p.degree) ↔ (3 ≤ p.degree) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ)  :
    (2 ≤ p.degree) ↔ (3 ≤ p.degree) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≥ 4 *‖p.derivative.eval z‖

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≥ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≥ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≥ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≥ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≥ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≥ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≥ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≥ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≥ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≥ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≥ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≥ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≥ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≥ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : Polynomial ℂ) (hp : p.degree ≥ 2) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ) :
    (2 ≤ p.degree) ↔ (p.degree ≥ 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ) :
    (2 ≤ p.degree) ↔ (p.degree ≥ 2) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ) :
    (2 ≤ p.degree) ↔ (p.degree ≥ 2) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ) :
    (2 ≤ p.degree) ↔ (p.degree ≥ 2) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ) :
    (2 ≤ p.degree) ↔ (p.degree ≥ 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ) :
    (2 ≤ p.degree) ↔ (p.degree ≥ 2) := by
  omega

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ) :
    (2 ≤ p.degree) ↔ (p.degree ≥ 2) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ) :
    (2 ≤ p.degree) ↔ (p.degree ≥ 2) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) ↔
    (∀ (p : Polynomial ℂ) (hp : p.degree ≥ 2) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) ↔
    (∀ (p : Polynomial ℂ) (hp : p.degree ≥ 2) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) ↔
    (∀ (p : Polynomial ℂ) (hp : p.degree ≥ 2) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) ↔
    (∀ (p : Polynomial ℂ) (hp : p.degree ≥ 2) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c₁ : ℂ, p.derivative.eval c₁ = 0 ∧
      ‖p.eval z - p.eval c₁‖ / ‖z - c₁‖ ≤ 4 *‖p.derivative.eval z‖

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ) :
    (∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) ↔ (∃ c₁ : ℂ, p.derivative.eval c₁ = 0 ∧
      ‖p.eval z - p.eval c₁‖ / ‖z - c₁‖ ≤ 4 *‖p.derivative.eval z‖) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ) :
    (∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) ↔ (∃ c₁ : ℂ, p.derivative.eval c₁ = 0 ∧
      ‖p.eval z - p.eval c₁‖ / ‖z - c₁‖ ≤ 4 *‖p.derivative.eval z‖) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ) :
    (∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) ↔ (∃ c₁ : ℂ, p.derivative.eval c₁ = 0 ∧
      ‖p.eval z - p.eval c₁‖ / ‖z - c₁‖ ≤ 4 *‖p.derivative.eval z‖) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ) :
    (∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) ↔ (∃ c₁ : ℂ, p.derivative.eval c₁ = 0 ∧
      ‖p.eval z - p.eval c₁‖ / ‖z - c₁‖ ≤ 4 *‖p.derivative.eval z‖) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ) :
    (∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) ↔ (∃ c₁ : ℂ, p.derivative.eval c₁ = 0 ∧
      ‖p.eval z - p.eval c₁‖ / ‖z - c₁‖ ≤ 4 *‖p.derivative.eval z‖) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ) :
    (∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) ↔ (∃ c₁ : ℂ, p.derivative.eval c₁ = 0 ∧
      ‖p.eval z - p.eval c₁‖ / ‖z - c₁‖ ≤ 4 *‖p.derivative.eval z‖) := by
  omega

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ) :
    (∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) ↔ (∃ c₁ : ℂ, p.derivative.eval c₁ = 0 ∧
      ‖p.eval z - p.eval c₁‖ / ‖z - c₁‖ ≤ 4 *‖p.derivative.eval z‖) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ) :
    (∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) ↔ (∃ c₁ : ℂ, p.derivative.eval c₁ = 0 ∧
      ‖p.eval z - p.eval c₁‖ / ‖z - c₁‖ ≤ 4 *‖p.derivative.eval z‖) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) ↔
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c₁ : ℂ, p.derivative.eval c₁ = 0 ∧
      ‖p.eval z - p.eval c₁‖ / ‖z - c₁‖ ≤ 4 *‖p.derivative.eval z‖) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) ↔
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c₁ : ℂ, p.derivative.eval c₁ = 0 ∧
      ‖p.eval z - p.eval c₁‖ / ‖z - c₁‖ ≤ 4 *‖p.derivative.eval z‖) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) ↔
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c₁ : ℂ, p.derivative.eval c₁ = 0 ∧
      ‖p.eval z - p.eval c₁‖ / ‖z - c₁‖ ≤ 4 *‖p.derivative.eval z‖) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) ↔
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c₁ : ℂ, p.derivative.eval c₁ = 0 ∧
      ‖p.eval z - p.eval c₁‖ / ‖z - c₁‖ ≤ 4 *‖p.derivative.eval z‖) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : Polynomial ℂ) (hp₀ : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) ↔
    (∀ (p : Polynomial ℂ) (hp₀ : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) ↔
    (∀ (p : Polynomial ℂ) (hp₀ : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) ↔
    (∀ (p : Polynomial ℂ) (hp₀ : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) ↔
    (∀ (p : Polynomial ℂ) (hp₀ : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : Polynomial ℂ) (hp : p.degree ≥ 2) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ < 4 *‖p.derivative.eval z‖

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : p.degree ≥ 2) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ < 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : p.degree ≥ 2) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ < 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : p.degree ≥ 2) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ < 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : p.degree ≥ 2) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ < 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : p.degree ≥ 2) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ < 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : p.degree ≥ 2) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ < 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : p.degree ≥ 2) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ < 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : Polynomial ℂ) (hp : p.degree > 2) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : p.degree > 2) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : p.degree > 2) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : p.degree > 2) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : p.degree > 2) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : p.degree > 2) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : p.degree > 2) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : p.degree > 2) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ)  :
    (2 ≤ p.degree) ↔ (p.degree > 2) := by
  omega

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ)  :
    (2 ≤ p.degree) ↔ (p.degree > 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ)  :
    (2 ≤ p.degree) ↔ (p.degree > 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ)  :
    (2 ≤ p.degree) ↔ (p.degree > 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ)  :
    (2 ≤ p.degree) ↔ (p.degree > 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ)  :
    (2 ≤ p.degree) ↔ (p.degree > 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ)  :
    (2 ≤ p.degree) ↔ (p.degree > 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : Polynomial ℂ) (hp : p.degree ≥ 3) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : p.degree ≥ 3) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : p.degree ≥ 3) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : p.degree ≥ 3) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : p.degree ≥ 3) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : p.degree ≥ 3) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : p.degree ≥ 3) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : p.degree ≥ 3) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ)  :
    (2 ≤ p.degree) ↔ (p.degree ≥ 3) := by
  omega

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ)  :
    (2 ≤ p.degree) ↔ (p.degree ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ)  :
    (2 ≤ p.degree) ↔ (p.degree ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ)  :
    (2 ≤ p.degree) ↔ (p.degree ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ)  :
    (2 ≤ p.degree) ↔ (p.degree ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ)  :
    (2 ≤ p.degree) ↔ (p.degree ≥ 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ)  :
    (2 ≤ p.degree) ↔ (p.degree ≥ 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : Polynomial ℂ) (hp : p.degree ≥ 2) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≥ 4 *‖p.derivative.eval z‖

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : p.degree ≥ 2) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≥ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : p.degree ≥ 2) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≥ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : p.degree ≥ 2) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≥ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : p.degree ≥ 2) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≥ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : p.degree ≥ 2) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≥ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : p.degree ≥ 2) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≥ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : p.degree ≥ 2) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≥ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : p.degree ≥ 2) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≥ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : p.degree ≥ 2) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≥ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : p.degree ≥ 2) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≥ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : p.degree ≥ 2) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≥ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : p.degree ≥ 2) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≥ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : p.degree ≥ 2) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≥ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖) →
    (∀ (p : Polynomial ℂ) (hp : p.degree ≥ 2) (z : ℂ) (K : ℝ), ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≥ 4 *‖p.derivative.eval z‖) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ) (hp : 2 ≤ p.degree) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ) (hp : 2 ≤ p.degree) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ) (hp : 2 ≤ p.degree) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ) (hp : 2 ≤ p.degree) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (p : Polynomial ℂ) (z : ℂ) (K : ℝ) (hp : 2 ≤ p.degree) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
