import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Algebra.Powerfree
/-!
# Erdős Problem 978

*Reference:*
 - [erdosproblems.com/978](https://www.erdosproblems.com/978)
 - [Ho67] Hooley, C., On the power free values of polynomials. Mathematika (1967), 21--26.
 - [Br11] Browning, T. D., Power-free values of polynomials. Arch. Math. (Basel) (2011), 139--150.
 - [Er53] Erdős, P., Arithmetical properties of polynomials. J. London Math. Soc. (1953), 416--425.
 - [OAI26a] OpenAI, *Squarefree values of quartics and power-free values of polynomials*. OpenAI
   Math Release preprint (2026).
   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Squarefree-values-of-quartics-and-power-free-values-of-polynomials-September-24-2026/manuscript.pdf
-/

section

open Polynomial Set

namespace Erdos978

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℤ[X]} (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) →
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) →
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) →
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) →
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) →
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) →
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) →
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)) :
    (9 ≤ f.natDegree) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)) :
    (9 ≤ f.natDegree) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)) :
    (9 ≤ f.natDegree) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)) :
    (9 ≤ f.natDegree) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)) :
    (9 ≤ f.natDegree) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)) :
    (9 ≤ f.natDegree) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)) :
    (9 ≤ f.natDegree) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 < f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) →
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 < f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) →
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 < f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) →
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 < f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) →
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 < f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) →
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 < f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) →
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 < f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) →
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 < f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)) :
    (9 ≤ f.natDegree) ↔ (9 < f.natDegree) := by
  omega

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)) :
    (9 ≤ f.natDegree) ↔ (9 < f.natDegree) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)) :
    (9 ≤ f.natDegree) ↔ (9 < f.natDegree) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)) :
    (9 ≤ f.natDegree) ↔ (9 < f.natDegree) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)) :
    (9 ≤ f.natDegree) ↔ (9 < f.natDegree) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)) :
    (9 ≤ f.natDegree) ↔ (9 < f.natDegree) := by
  simp_all

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)) :
    (9 ≤ f.natDegree) ↔ (9 < f.natDegree) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 10 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) →
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 10 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) →
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 10 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) →
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 10 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) →
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 10 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) →
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 10 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) →
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 10 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) →
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 10 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)) :
    (9 ≤ f.natDegree) ↔ (10 ≤ f.natDegree) := by
  omega

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)) :
    (9 ≤ f.natDegree) ↔ (10 ≤ f.natDegree) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)) :
    (9 ≤ f.natDegree) ↔ (10 ≤ f.natDegree) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)) :
    (9 ≤ f.natDegree) ↔ (10 ≤ f.natDegree) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)) :
    (9 ≤ f.natDegree) ↔ (10 ≤ f.natDegree) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)) :
    (9 ≤ f.natDegree) ↔ (10 ≤ f.natDegree) := by
  simp_all

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)) :
    (9 ≤ f.natDegree) ↔ (10 ≤ f.natDegree) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℤ[X]} (hi : Irreducible f) (hd : f.natDegree ≥ 9) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} :
    (9 ≤ f.natDegree) ↔ (f.natDegree ≥ 9) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} :
    (9 ≤ f.natDegree) ↔ (f.natDegree ≥ 9) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} :
    (9 ≤ f.natDegree) ↔ (f.natDegree ≥ 9) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} :
    (9 ≤ f.natDegree) ↔ (f.natDegree ≥ 9) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} :
    (9 ≤ f.natDegree) ↔ (f.natDegree ≥ 9) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} :
    (9 ≤ f.natDegree) ↔ (f.natDegree ≥ 9) := by
  omega

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} :
    (9 ≤ f.natDegree) ↔ (f.natDegree ≥ 9) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} :
    (9 ≤ f.natDegree) ↔ (f.natDegree ≥ 9) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) ↔
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : f.natDegree ≥ 9) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) ↔
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : f.natDegree ≥ 9) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) ↔
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : f.natDegree ≥ 9) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) ↔
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : f.natDegree ≥ 9) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℤ[X]} (hd : 9 ≤ f.natDegree) (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) ↔
    (∀ {f : ℤ[X]} (hd : 9 ≤ f.natDegree) (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) ↔
    (∀ {f : ℤ[X]} (hd : 9 ≤ f.natDegree) (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) ↔
    (∀ {f : ℤ[X]} (hd : 9 ≤ f.natDegree) (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) ↔
    (∀ {f : ℤ[X]} (hd : 9 ≤ f.natDegree) (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℤ[X]} (hi₀ : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) ↔
    (∀ {f : ℤ[X]} (hi₀ : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) ↔
    (∀ {f : ℤ[X]} (hi₀ : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) ↔
    (∀ {f : ℤ[X]} (hi₀ : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) ↔
    (∀ {f : ℤ[X]} (hi₀ : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℤ[X]} (hi : Irreducible f) (hd : f.natDegree > 9) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) →
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : f.natDegree > 9) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) →
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : f.natDegree > 9) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) →
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : f.natDegree > 9) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) →
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : f.natDegree > 9) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) →
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : f.natDegree > 9) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) →
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : f.natDegree > 9) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) →
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : f.natDegree > 9) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)) :
    (9 ≤ f.natDegree) ↔ (f.natDegree > 9) := by
  omega

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)) :
    (9 ≤ f.natDegree) ↔ (f.natDegree > 9) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)) :
    (9 ≤ f.natDegree) ↔ (f.natDegree > 9) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)) :
    (9 ≤ f.natDegree) ↔ (f.natDegree > 9) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)) :
    (9 ≤ f.natDegree) ↔ (f.natDegree > 9) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)) :
    (9 ≤ f.natDegree) ↔ (f.natDegree > 9) := by
  simp_all

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)) :
    (9 ≤ f.natDegree) ↔ (f.natDegree > 9) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℤ[X]} (hi : Irreducible f) (hd : f.natDegree ≥ 10) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) →
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : f.natDegree ≥ 10) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) →
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : f.natDegree ≥ 10) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) →
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : f.natDegree ≥ 10) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) →
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : f.natDegree ≥ 10) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) →
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : f.natDegree ≥ 10) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) →
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : f.natDegree ≥ 10) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) →
    (∀ {f : ℤ[X]} (hi : Irreducible f) (hd : f.natDegree ≥ 10) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)), {n : ℕ | Powerfree (f.natDegree - 2) (f.eval (n : ℤ))}.Infinite) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)) :
    (9 ≤ f.natDegree) ↔ (f.natDegree ≥ 10) := by
  omega

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)) :
    (9 ≤ f.natDegree) ↔ (f.natDegree ≥ 10) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)) :
    (9 ≤ f.natDegree) ↔ (f.natDegree ≥ 10) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)) :
    (9 ≤ f.natDegree) ↔ (f.natDegree ≥ 10) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)) :
    (9 ≤ f.natDegree) ↔ (f.natDegree ≥ 10) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)) :
    (9 ≤ f.natDegree) ↔ (f.natDegree ≥ 10) := by
  simp_all

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} (hi : Irreducible f) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)) :
    (9 ≤ f.natDegree) ↔ (f.natDegree ≥ 10) := by
  plausible

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {f : ℤ[X]} (hi : Irreducible f) (hd : 9 ≤ f.natDegree) (hp : ∀ (p : ℕ), p.Prime → ∃ n : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 2) ∣ f.eval (n : ℤ)) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
