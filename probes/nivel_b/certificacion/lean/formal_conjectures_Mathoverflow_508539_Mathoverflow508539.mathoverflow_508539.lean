import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Boundary
--   import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Hypercube
/-!
# MathOverflow 508539

Edge-vertex inequality $EV \geq 4^{n-1}$.

*References:*
- [MathOverflow 508539](https://mathoverflow.net/questions/508539), asked by
  [Paata Ivanisvili](https://mathoverflow.net/users/50901/paata-ivanisvili).
- [DIRX26] Durcik, P., Ivanisvili, P., Roos, J., and Xie, X.,
  *Sharp isoperimetric inequalities on the Hamming cube II: The critical exponent* (2026),
  [arXiv:2602.20462](https://arxiv.org/abs/2602.20462), inequality (1.2).
-/

section

open SimpleGraph
open scoped Finset

namespace Mathoverflow508539

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) :
    (0 < n) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) :
    (0 < n) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) :
    (0 < n) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) < #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) < #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) < #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) < #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) < #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) < #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) < #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) < #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hn : 0 < n) :
    (#A = 2 ^ (n - 1)) ↔ (#A = 3 ^ (n - 1)) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hn : 0 < n) :
    (#A = 2 ^ (n - 1)) ↔ (#A = 3 ^ (n - 1)) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hn : 0 < n) :
    (#A = 2 ^ (n - 1)) ↔ (#A = 3 ^ (n - 1)) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hn : 0 < n) :
    (#A = 2 ^ (n - 1)) ↔ (#A = 3 ^ (n - 1)) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hn : 0 < n) :
    (#A = 2 ^ (n - 1)) ↔ (#A = 3 ^ (n - 1)) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hn : 0 < n) :
    (#A = 2 ^ (n - 1)) ↔ (#A = 3 ^ (n - 1)) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hn : 0 < n) :
    (#A = 2 ^ (n - 1)) ↔ (#A = 3 ^ (n - 1)) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≥ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≥ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≥ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≥ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≥ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≥ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≥ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≥ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≥ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≥ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≥ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≥ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≥ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≥ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≥ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : n > 0), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) :
    (0 < n) ↔ (n > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) :
    (0 < n) ↔ (n > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) :
    (0 < n) ↔ (n > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) :
    (0 < n) ↔ (n > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) :
    (0 < n) ↔ (n > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) :
    (0 < n) ↔ (n > 0) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) :
    (0 < n) ↔ (n > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) :
    (0 < n) ↔ (n > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) ↔
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : n > 0), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) ↔
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : n > 0), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) ↔
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : n > 0), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) ↔
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : n > 0), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) ≥ 4 ^ (n - 1)

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) :
    (4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) ↔ (#((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) ≥ 4 ^ (n - 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) :
    (4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) ↔ (#((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) ≥ 4 ^ (n - 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) :
    (4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) ↔ (#((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) ≥ 4 ^ (n - 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) :
    (4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) ↔ (#((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) ≥ 4 ^ (n - 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) :
    (4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) ↔ (#((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) ≥ 4 ^ (n - 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) :
    (4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) ↔ (#((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) ≥ 4 ^ (n - 1)) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) :
    (4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) ↔ (#((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) ≥ 4 ^ (n - 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) :
    (4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) ↔ (#((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) ≥ 4 ^ (n - 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) ↔
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) ≥ 4 ^ (n - 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) ↔
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) ≥ 4 ^ (n - 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) ↔
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) ≥ 4 ^ (n - 1)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) ↔
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) ≥ 4 ^ (n - 1)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hn : 0 < n) (hA : #A = 2 ^ (n - 1)), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) ↔
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hn : 0 < n) (hA : #A = 2 ^ (n - 1)), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) ↔
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hn : 0 < n) (hA : #A = 2 ^ (n - 1)), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) ↔
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hn : 0 < n) (hA : #A = 2 ^ (n - 1)), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) ↔
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hn : 0 < n) (hA : #A = 2 ^ (n - 1)), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA₀ : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) ↔
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA₀ : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) ↔
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA₀ : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) ↔
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA₀ : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) ↔
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA₀ : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : ¬(n ≤ 0)), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) ↔
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : ¬(n ≤ 0)), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) ↔
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : ¬(n ≤ 0)), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) ↔
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : ¬(n ≤ 0)), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) ↔
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : ¬(n ≤ 0)), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 1 ≤ n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) :
    (0 < n) ↔ (1 ≤ n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) :
    (0 < n) ↔ (1 ≤ n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) :
    (0 < n) ↔ (1 ≤ n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) :
    (0 < n) ↔ (1 ≤ n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) :
    (0 < n) ↔ (1 ≤ n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) :
    (0 < n) ↔ (1 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) :
    (0 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) :
    (0 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) ↔
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 1 ≤ n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) ↔
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 1 ≤ n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) ↔
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 1 ≤ n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) ↔
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 1 ≤ n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : n > 0), 4 ^ (n - 1) < #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : n > 0), 4 ^ (n - 1) < #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : n > 0), 4 ^ (n - 1) < #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : n > 0), 4 ^ (n - 1) < #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : n > 0), 4 ^ (n - 1) < #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : n > 0), 4 ^ (n - 1) < #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : n > 0), 4 ^ (n - 1) < #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : n > 0), 4 ^ (n - 1) < #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : n > 0), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : n > 0), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : n > 0), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : n > 0), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : n > 0), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : n > 0), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : n > 0), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : n > 0), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : n > 0), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : n > 0), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : n > 0), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : n > 0), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : n > 0), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : n > 0), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : n > 0), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hn : 0 < n) :
    (#A = 2 ^ (n - 1)) ↔ (#A = 3 ^ (n - 1)) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hn : 0 < n) :
    (#A = 2 ^ (n - 1)) ↔ (#A = 3 ^ (n - 1)) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hn : 0 < n) :
    (#A = 2 ^ (n - 1)) ↔ (#A = 3 ^ (n - 1)) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hn : 0 < n) :
    (#A = 2 ^ (n - 1)) ↔ (#A = 3 ^ (n - 1)) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hn : 0 < n) :
    (#A = 2 ^ (n - 1)) ↔ (#A = 3 ^ (n - 1)) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hn : 0 < n) :
    (#A = 2 ^ (n - 1)) ↔ (#A = 3 ^ (n - 1)) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hn : 0 < n) :
    (#A = 2 ^ (n - 1)) ↔ (#A = 3 ^ (n - 1)) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : n > 0), 4 ^ (n - 1) ≥ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : n > 0), 4 ^ (n - 1) ≥ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : n > 0), 4 ^ (n - 1) ≥ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : n > 0), 4 ^ (n - 1) ≥ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : n > 0), 4 ^ (n - 1) ≥ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : n > 0), 4 ^ (n - 1) ≥ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : n > 0), 4 ^ (n - 1) ≥ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : n > 0), 4 ^ (n - 1) ≥ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : n > 0), 4 ^ (n - 1) ≥ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : n > 0), 4 ^ (n - 1) ≥ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : n > 0), 4 ^ (n - 1) ≥ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : n > 0), 4 ^ (n - 1) ≥ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : n > 0), 4 ^ (n - 1) ≥ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : n > 0), 4 ^ (n - 1) ≥ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : n > 0), 4 ^ (n - 1) ≥ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) > 4 ^ (n - 1)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) > 4 ^ (n - 1)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) > 4 ^ (n - 1)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) > 4 ^ (n - 1)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) > 4 ^ (n - 1)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) > 4 ^ (n - 1)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) > 4 ^ (n - 1)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) > 4 ^ (n - 1)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : 0 < n), #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) ≥ 4 ^ (n - 1)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : 0 < n), #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) ≥ 4 ^ (n - 1)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : 0 < n), #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) ≥ 4 ^ (n - 1)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : 0 < n), #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) ≥ 4 ^ (n - 1)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : 0 < n), #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) ≥ 4 ^ (n - 1)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : 0 < n), #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) ≥ 4 ^ (n - 1)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : 0 < n), #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) ≥ 4 ^ (n - 1)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : 0 < n), #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) ≥ 4 ^ (n - 1)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : 0 < n), #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) ≥ 4 ^ (n - 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : 0 < n), #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) ≥ 4 ^ (n - 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : 0 < n), #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) ≥ 4 ^ (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : 0 < n), #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) ≥ 4 ^ (n - 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : 0 < n), #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) ≥ 4 ^ (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : 0 < n), #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) ≥ 4 ^ (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : 0 < n), #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) ≥ 4 ^ (n - 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hn : 0 < n) :
    (#A = 2 ^ (n - 1)) ↔ (#A = 3 ^ (n - 1)) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hn : 0 < n) :
    (#A = 2 ^ (n - 1)) ↔ (#A = 3 ^ (n - 1)) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hn : 0 < n) :
    (#A = 2 ^ (n - 1)) ↔ (#A = 3 ^ (n - 1)) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hn : 0 < n) :
    (#A = 2 ^ (n - 1)) ↔ (#A = 3 ^ (n - 1)) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hn : 0 < n) :
    (#A = 2 ^ (n - 1)) ↔ (#A = 3 ^ (n - 1)) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hn : 0 < n) :
    (#A = 2 ^ (n - 1)) ↔ (#A = 3 ^ (n - 1)) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hn : 0 < n) :
    (#A = 2 ^ (n - 1)) ↔ (#A = 3 ^ (n - 1)) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) ≤ 4 ^ (n - 1)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) ≤ 4 ^ (n - 1)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) ≤ 4 ^ (n - 1)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) ≤ 4 ^ (n - 1)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) ≤ 4 ^ (n - 1)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) ≤ 4 ^ (n - 1)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) ≤ 4 ^ (n - 1)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) ≤ 4 ^ (n - 1)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) ≤ 4 ^ (n - 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) ≤ 4 ^ (n - 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) ≤ 4 ^ (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) ≤ 4 ^ (n - 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) ≤ 4 ^ (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) ≤ 4 ^ (n - 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A) ≤ 4 ^ (n - 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 1 ≤ n), 4 ^ (n - 1) < #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 1 ≤ n), 4 ^ (n - 1) < #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 1 ≤ n), 4 ^ (n - 1) < #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 1 ≤ n), 4 ^ (n - 1) < #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 1 ≤ n), 4 ^ (n - 1) < #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 1 ≤ n), 4 ^ (n - 1) < #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 1 ≤ n), 4 ^ (n - 1) < #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 1 ≤ n), 4 ^ (n - 1) < #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 1 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 1 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 1 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 1 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 1 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 1 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 1 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 1 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) :
    (0 < n) ↔ (1 < n) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) :
    (0 < n) ↔ (1 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) :
    (0 < n) ↔ (1 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : 1 ≤ n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : 1 ≤ n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : 1 ≤ n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : 1 ≤ n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : 1 ≤ n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : 1 ≤ n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : 1 ≤ n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : 1 ≤ n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : 1 ≤ n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : 1 ≤ n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : 1 ≤ n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : 1 ≤ n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : 1 ≤ n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : 1 ≤ n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 3 ^ (n - 1)) (hn : 1 ≤ n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hn : 0 < n) :
    (#A = 2 ^ (n - 1)) ↔ (#A = 3 ^ (n - 1)) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hn : 0 < n) :
    (#A = 2 ^ (n - 1)) ↔ (#A = 3 ^ (n - 1)) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hn : 0 < n) :
    (#A = 2 ^ (n - 1)) ↔ (#A = 3 ^ (n - 1)) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hn : 0 < n) :
    (#A = 2 ^ (n - 1)) ↔ (#A = 3 ^ (n - 1)) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hn : 0 < n) :
    (#A = 2 ^ (n - 1)) ↔ (#A = 3 ^ (n - 1)) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hn : 0 < n) :
    (#A = 2 ^ (n - 1)) ↔ (#A = 3 ^ (n - 1)) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hn : 0 < n) :
    (#A = 2 ^ (n - 1)) ↔ (#A = 3 ^ (n - 1)) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 1 ≤ n), 4 ^ (n - 1) ≥ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 1 ≤ n), 4 ^ (n - 1) ≥ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 1 ≤ n), 4 ^ (n - 1) ≥ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 1 ≤ n), 4 ^ (n - 1) ≥ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 1 ≤ n), 4 ^ (n - 1) ≥ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 1 ≤ n), 4 ^ (n - 1) ≥ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 1 ≤ n), 4 ^ (n - 1) ≥ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 1 ≤ n), 4 ^ (n - 1) ≥ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 1 ≤ n), 4 ^ (n - 1) ≥ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 1 ≤ n), 4 ^ (n - 1) ≥ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 1 ≤ n), 4 ^ (n - 1) ≥ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 1 ≤ n), 4 ^ (n - 1) ≥ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 1 ≤ n), 4 ^ (n - 1) ≥ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 1 ≤ n), 4 ^ (n - 1) ≥ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 1 ≤ n), 4 ^ (n - 1) ≥ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) →
    (∀ {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n), 4 ^ (n - 1) ≤ #((hypercube n).edgeBoundary A) *
      #((hypercube n).innerVertexBoundary A)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) :
    (0 < n) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) :
    (0 < n) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) :
    (0 < n) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} (A : Finset (Fin n → Bool)) (hA : #A = 2 ^ (n - 1)) (hn : 0 < n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
