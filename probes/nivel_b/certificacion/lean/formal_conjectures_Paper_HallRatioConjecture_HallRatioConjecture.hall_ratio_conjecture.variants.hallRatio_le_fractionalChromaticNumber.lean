import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.FractionalChromaticNumber
/-!
# The Hall ratio conjecture (Harris 2019) — disproved

*References:*
* [Ha19] Harris, D. G. (2019). "Some results on chromatic number as a function of triangle
  count." *SIAM J. Discrete Math.* 33, pp. 546--563.
* [DOW20] Dvořák, Z., Ossona de Mendez, P. and Wu, H. (2020). "1-subdivisions, the fractional
  chromatic number and the Hall ratio." *Combinatorica* 40, pp. 759--774.
  [arXiv:1812.07327](https://arxiv.org/abs/1812.07327)
* [BLMNPV22] Blumenthal, A., Lidický, B., Martin, R. R., Norin, S., Pfender, F. and Volec, J.
  (2022). "Counterexamples to a conjecture of Harris on Hall ratio." *SIAM J. Discrete Math.*
  36, pp. 1678--1686. [arXiv:1811.11116](https://arxiv.org/abs/1811.11116)
* [SU97] Scheinerman, E. R. and Ullman, D. H. (1997). *Fractional Graph Theory.* Wiley.
-/

section

open SimpleGraph

namespace HallRatioConjecture

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The **Hall ratio** `ρ(G)`: the maximum of `|V(H)| / α(H)` over nonempty induced subgraphs
`H` of `G` (`α` the independence number). -/
noncomputable def hallRatio (G : SimpleGraph V) : ℝ :=
  sSup {r | ∃ S : Finset V, S.Nonempty ∧
    r = (S.card : ℝ) / ((G.induce (S : Set V)).indepNum : ℝ)}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G < G.fractionalChromaticNumber

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G < G.fractionalChromaticNumber) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G < G.fractionalChromaticNumber) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G < G.fractionalChromaticNumber) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G < G.fractionalChromaticNumber) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G < G.fractionalChromaticNumber) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G < G.fractionalChromaticNumber) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G < G.fractionalChromaticNumber) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≥ G.fractionalChromaticNumber

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≥ G.fractionalChromaticNumber) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≥ G.fractionalChromaticNumber) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≥ G.fractionalChromaticNumber) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≥ G.fractionalChromaticNumber) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≥ G.fractionalChromaticNumber) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≥ G.fractionalChromaticNumber) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≥ G.fractionalChromaticNumber) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≥ G.fractionalChromaticNumber) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≥ G.fractionalChromaticNumber) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≥ G.fractionalChromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≥ G.fractionalChromaticNumber) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≥ G.fractionalChromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≥ G.fractionalChromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≥ G.fractionalChromaticNumber) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), G.fractionalChromaticNumber ≥ hallRatio G

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    (hallRatio G ≤ G.fractionalChromaticNumber) ↔ (G.fractionalChromaticNumber ≥ hallRatio G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    (hallRatio G ≤ G.fractionalChromaticNumber) ↔ (G.fractionalChromaticNumber ≥ hallRatio G) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    (hallRatio G ≤ G.fractionalChromaticNumber) ↔ (G.fractionalChromaticNumber ≥ hallRatio G) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    (hallRatio G ≤ G.fractionalChromaticNumber) ↔ (G.fractionalChromaticNumber ≥ hallRatio G) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    (hallRatio G ≤ G.fractionalChromaticNumber) ↔ (G.fractionalChromaticNumber ≥ hallRatio G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    (hallRatio G ≤ G.fractionalChromaticNumber) ↔ (G.fractionalChromaticNumber ≥ hallRatio G) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    (hallRatio G ≤ G.fractionalChromaticNumber) ↔ (G.fractionalChromaticNumber ≥ hallRatio G) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    (hallRatio G ≤ G.fractionalChromaticNumber) ↔ (G.fractionalChromaticNumber ≥ hallRatio G) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), G.fractionalChromaticNumber ≥ hallRatio G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), G.fractionalChromaticNumber ≥ hallRatio G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), G.fractionalChromaticNumber ≥ hallRatio G) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), G.fractionalChromaticNumber ≥ hallRatio G) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), G.fractionalChromaticNumber > hallRatio G

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), G.fractionalChromaticNumber > hallRatio G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), G.fractionalChromaticNumber > hallRatio G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), G.fractionalChromaticNumber > hallRatio G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), G.fractionalChromaticNumber > hallRatio G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), G.fractionalChromaticNumber > hallRatio G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), G.fractionalChromaticNumber > hallRatio G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), G.fractionalChromaticNumber > hallRatio G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), G.fractionalChromaticNumber ≤ hallRatio G

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), G.fractionalChromaticNumber ≤ hallRatio G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), G.fractionalChromaticNumber ≤ hallRatio G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), G.fractionalChromaticNumber ≤ hallRatio G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), G.fractionalChromaticNumber ≤ hallRatio G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), G.fractionalChromaticNumber ≤ hallRatio G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), G.fractionalChromaticNumber ≤ hallRatio G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), G.fractionalChromaticNumber ≤ hallRatio G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), G.fractionalChromaticNumber ≤ hallRatio G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), G.fractionalChromaticNumber ≤ hallRatio G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), G.fractionalChromaticNumber ≤ hallRatio G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), G.fractionalChromaticNumber ≤ hallRatio G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), G.fractionalChromaticNumber ≤ hallRatio G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), G.fractionalChromaticNumber ≤ hallRatio G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), hallRatio G ≤ G.fractionalChromaticNumber) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), G.fractionalChromaticNumber ≤ hallRatio G) := by
  intro h; intros; aesop

#eval "FIN_CERTIFICAR"
