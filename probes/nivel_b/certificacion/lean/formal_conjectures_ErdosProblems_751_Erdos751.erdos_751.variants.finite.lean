import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Circumference
/-!
# Erdős Problem 751

*References:*
- [erdosproblems.com/751](https://www.erdosproblems.com/751)
- [Er94b] Erdős, Paul, Some problems in number theory, combinatorics and combinatorial geometry.
  Math. Pannon. (1994), 261--269.
- [BoVi98] Bondy, J. A. and Vince, A., Cycles in a graph whose lengths differ by one or two.
  J. Graph Theory (1998), 11--15.
-/

section

namespace Erdos751

universe u_c1 u_c2 u_c3 u_c4 u_c5 u_c6 u_c7 u_c8 u_c9 u_c10 u_c11 u_c12 u_c13 u_c14 u_c15 u_c16 u_c17 u_c18 u_c19 u_c20 u_c21 u_c22 u_c23 u_c24 u_c25
set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c1} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c2} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj], ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c2} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj], ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c1} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c2} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj], ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c1} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c2} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj], ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c1} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c2} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj], ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c1} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c2} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj], ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c1} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c2} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj], ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c1} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c2} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj], ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c1} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type u_c3} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    ((4 : ℕ∞) ≤ G.chromaticNumber) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type u_c3} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    ((4 : ℕ∞) ≤ G.chromaticNumber) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type u_c3} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    ((4 : ℕ∞) ≤ G.chromaticNumber) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type u_c3} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    ((4 : ℕ∞) ≤ G.chromaticNumber) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type u_c3} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    ((4 : ℕ∞) ≤ G.chromaticNumber) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type u_c3} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    ((4 : ℕ∞) ≤ G.chromaticNumber) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type u_c3} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    ((4 : ℕ∞) ≤ G.chromaticNumber) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c4} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c5} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) < G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c4} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c5} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) < G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c4} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c5} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) < G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c4} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c5} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) < G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c4} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c5} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) < G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c4} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c5} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) < G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c4} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c5} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) < G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c4} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c5} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) < G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type u_c6} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    ((4 : ℕ∞) ≤ G.chromaticNumber) ↔ ((4 : ℕ∞) < G.chromaticNumber) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type u_c6} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    ((4 : ℕ∞) ≤ G.chromaticNumber) ↔ ((4 : ℕ∞) < G.chromaticNumber) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type u_c6} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    ((4 : ℕ∞) ≤ G.chromaticNumber) ↔ ((4 : ℕ∞) < G.chromaticNumber) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type u_c6} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    ((4 : ℕ∞) ≤ G.chromaticNumber) ↔ ((4 : ℕ∞) < G.chromaticNumber) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type u_c6} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    ((4 : ℕ∞) ≤ G.chromaticNumber) ↔ ((4 : ℕ∞) < G.chromaticNumber) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type u_c6} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    ((4 : ℕ∞) ≤ G.chromaticNumber) ↔ ((4 : ℕ∞) < G.chromaticNumber) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type u_c6} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    ((4 : ℕ∞) ≤ G.chromaticNumber) ↔ ((4 : ℕ∞) < G.chromaticNumber) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c7} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c8} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (5 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c8} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (5 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c7} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c8} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (5 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c7} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c8} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (5 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c7} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c8} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (5 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c7} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c8} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (5 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c7} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c8} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (5 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c7} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c8} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (5 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c7} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c7} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c8} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (5 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c7} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c8} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (5 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c7} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c8} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (5 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c7} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c8} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (5 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c7} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c8} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (5 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c7} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c8} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (5 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c7} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c8} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (5 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type u_c9} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    ((4 : ℕ∞) ≤ G.chromaticNumber) ↔ ((5 : ℕ∞) ≤ G.chromaticNumber) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type u_c9} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    ((4 : ℕ∞) ≤ G.chromaticNumber) ↔ ((5 : ℕ∞) ≤ G.chromaticNumber) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type u_c9} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    ((4 : ℕ∞) ≤ G.chromaticNumber) ↔ ((5 : ℕ∞) ≤ G.chromaticNumber) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type u_c9} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    ((4 : ℕ∞) ≤ G.chromaticNumber) ↔ ((5 : ℕ∞) ≤ G.chromaticNumber) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type u_c9} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    ((4 : ℕ∞) ≤ G.chromaticNumber) ↔ ((5 : ℕ∞) ≤ G.chromaticNumber) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type u_c9} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    ((4 : ℕ∞) ≤ G.chromaticNumber) ↔ ((5 : ℕ∞) ≤ G.chromaticNumber) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type u_c9} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    ((4 : ℕ∞) ≤ G.chromaticNumber) ↔ ((5 : ℕ∞) ≤ G.chromaticNumber) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c10} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c11} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.chromaticNumber ≥ (4 : ℕ∞)), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2

set_option maxHeartbeats 200000 in
example {V : Type u_c12} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((4 : ℕ∞) ≤ G.chromaticNumber) ↔ (G.chromaticNumber ≥ (4 : ℕ∞)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {V : Type u_c12} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((4 : ℕ∞) ≤ G.chromaticNumber) ↔ (G.chromaticNumber ≥ (4 : ℕ∞)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {V : Type u_c12} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((4 : ℕ∞) ≤ G.chromaticNumber) ↔ (G.chromaticNumber ≥ (4 : ℕ∞)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {V : Type u_c12} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((4 : ℕ∞) ≤ G.chromaticNumber) ↔ (G.chromaticNumber ≥ (4 : ℕ∞)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {V : Type u_c12} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((4 : ℕ∞) ≤ G.chromaticNumber) ↔ (G.chromaticNumber ≥ (4 : ℕ∞)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {V : Type u_c12} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((4 : ℕ∞) ≤ G.chromaticNumber) ↔ (G.chromaticNumber ≥ (4 : ℕ∞)) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type u_c12} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((4 : ℕ∞) ≤ G.chromaticNumber) ↔ (G.chromaticNumber ≥ (4 : ℕ∞)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {V : Type u_c12} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((4 : ℕ∞) ≤ G.chromaticNumber) ↔ (G.chromaticNumber ≥ (4 : ℕ∞)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c10} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) ↔
    (∀ {V : Type u_c11} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.chromaticNumber ≥ (4 : ℕ∞)), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c10} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) ↔
    (∀ {V : Type u_c11} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.chromaticNumber ≥ (4 : ℕ∞)), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c10} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) ↔
    (∀ {V : Type u_c11} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.chromaticNumber ≥ (4 : ℕ∞)), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c10} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) ↔
    (∀ {V : Type u_c11} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.chromaticNumber ≥ (4 : ℕ∞)), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c13} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c14} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m₁ ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m₁ < m' ∧ m' ≤ m₁ + 2

set_option maxHeartbeats 200000 in
example {V : Type u_c15} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) ↔ (∃ m₁ ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m₁ < m' ∧ m' ≤ m₁ + 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {V : Type u_c15} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) ↔ (∃ m₁ ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m₁ < m' ∧ m' ≤ m₁ + 2) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {V : Type u_c15} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) ↔ (∃ m₁ ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m₁ < m' ∧ m' ≤ m₁ + 2) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {V : Type u_c15} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) ↔ (∃ m₁ ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m₁ < m' ∧ m' ≤ m₁ + 2) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {V : Type u_c15} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) ↔ (∃ m₁ ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m₁ < m' ∧ m' ≤ m₁ + 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {V : Type u_c15} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) ↔ (∃ m₁ ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m₁ < m' ∧ m' ≤ m₁ + 2) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type u_c15} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) ↔ (∃ m₁ ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m₁ < m' ∧ m' ≤ m₁ + 2) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {V : Type u_c15} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) ↔ (∃ m₁ ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m₁ < m' ∧ m' ≤ m₁ + 2) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c13} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) ↔
    (∀ {V : Type u_c14} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m₁ ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m₁ < m' ∧ m' ≤ m₁ + 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c13} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) ↔
    (∀ {V : Type u_c14} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m₁ ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m₁ < m' ∧ m' ≤ m₁ + 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c13} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) ↔
    (∀ {V : Type u_c14} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m₁ ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m₁ < m' ∧ m' ≤ m₁ + 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c13} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) ↔
    (∀ {V : Type u_c14} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m₁ ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m₁ < m' ∧ m' ≤ m₁ + 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c16} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c17} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG₀ : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c16} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) ↔
    (∀ {V : Type u_c17} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG₀ : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c16} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) ↔
    (∀ {V : Type u_c17} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG₀ : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c16} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) ↔
    (∀ {V : Type u_c17} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG₀ : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c16} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) ↔
    (∀ {V : Type u_c17} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG₀ : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c19} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c20} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.chromaticNumber > (4 : ℕ∞)), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c19} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c20} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.chromaticNumber > (4 : ℕ∞)), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c19} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c20} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.chromaticNumber > (4 : ℕ∞)), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c19} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c20} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.chromaticNumber > (4 : ℕ∞)), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c19} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c20} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.chromaticNumber > (4 : ℕ∞)), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c19} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c20} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.chromaticNumber > (4 : ℕ∞)), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c19} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c20} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.chromaticNumber > (4 : ℕ∞)), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c19} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c20} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.chromaticNumber > (4 : ℕ∞)), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type u_c21} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    ((4 : ℕ∞) ≤ G.chromaticNumber) ↔ (G.chromaticNumber > (4 : ℕ∞)) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type u_c21} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    ((4 : ℕ∞) ≤ G.chromaticNumber) ↔ (G.chromaticNumber > (4 : ℕ∞)) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type u_c21} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    ((4 : ℕ∞) ≤ G.chromaticNumber) ↔ (G.chromaticNumber > (4 : ℕ∞)) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type u_c21} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    ((4 : ℕ∞) ≤ G.chromaticNumber) ↔ (G.chromaticNumber > (4 : ℕ∞)) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type u_c21} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    ((4 : ℕ∞) ≤ G.chromaticNumber) ↔ (G.chromaticNumber > (4 : ℕ∞)) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type u_c21} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    ((4 : ℕ∞) ≤ G.chromaticNumber) ↔ (G.chromaticNumber > (4 : ℕ∞)) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type u_c21} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    ((4 : ℕ∞) ≤ G.chromaticNumber) ↔ (G.chromaticNumber > (4 : ℕ∞)) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c22} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c23} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.chromaticNumber ≥ (5 : ℕ∞)), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c23} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.chromaticNumber ≥ (5 : ℕ∞)), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c22} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c23} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.chromaticNumber ≥ (5 : ℕ∞)), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c22} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c23} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.chromaticNumber ≥ (5 : ℕ∞)), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c22} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c23} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.chromaticNumber ≥ (5 : ℕ∞)), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c22} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c23} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.chromaticNumber ≥ (5 : ℕ∞)), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c22} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c23} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.chromaticNumber ≥ (5 : ℕ∞)), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c22} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c23} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.chromaticNumber ≥ (5 : ℕ∞)), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c22} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c22} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c23} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.chromaticNumber ≥ (5 : ℕ∞)), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c22} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c23} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.chromaticNumber ≥ (5 : ℕ∞)), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c22} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c23} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.chromaticNumber ≥ (5 : ℕ∞)), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c22} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c23} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.chromaticNumber ≥ (5 : ℕ∞)), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c22} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c23} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.chromaticNumber ≥ (5 : ℕ∞)), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c22} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c23} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.chromaticNumber ≥ (5 : ℕ∞)), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c22} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) →
    (∀ {V : Type u_c23} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.chromaticNumber ≥ (5 : ℕ∞)), ∃ m ∈ G.cycleLengths, ∃ m' ∈ G.cycleLengths, m < m' ∧ m' ≤ m + 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type u_c24} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    ((4 : ℕ∞) ≤ G.chromaticNumber) ↔ (G.chromaticNumber ≥ (5 : ℕ∞)) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type u_c24} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    ((4 : ℕ∞) ≤ G.chromaticNumber) ↔ (G.chromaticNumber ≥ (5 : ℕ∞)) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type u_c24} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    ((4 : ℕ∞) ≤ G.chromaticNumber) ↔ (G.chromaticNumber ≥ (5 : ℕ∞)) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type u_c24} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    ((4 : ℕ∞) ≤ G.chromaticNumber) ↔ (G.chromaticNumber ≥ (5 : ℕ∞)) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type u_c24} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    ((4 : ℕ∞) ≤ G.chromaticNumber) ↔ (G.chromaticNumber ≥ (5 : ℕ∞)) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type u_c24} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    ((4 : ℕ∞) ≤ G.chromaticNumber) ↔ (G.chromaticNumber ≥ (5 : ℕ∞)) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type u_c24} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]  :
    ((4 : ℕ∞) ≤ G.chromaticNumber) ↔ (G.chromaticNumber ≥ (5 : ℕ∞)) := by
  plausible

set_option maxHeartbeats 200000 in
example {V : Type u_c25} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {V : Type u_c25} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type u_c25} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {V : Type u_c25} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type u_c25} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : (4 : ℕ∞) ≤ G.chromaticNumber) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
