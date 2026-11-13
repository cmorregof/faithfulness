import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Combinatorics.LimitObjects.Graphon
/-!
# Sidorenko's conjecture (1993)

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Sidorenko%27s_conjecture)
* [Si93] Sidorenko, A. (1993). "A correlation inequality for bipartite graphs."
  *Graphs Combin.* 9, pp. 201--204.
* [CoFo10] Conlon, D. and Fox, J. (2010). "Bounds for graph regularity and removal lemmas."
  *Geom. Funct. Anal.* 22, pp. 1191--1256.
* [KLL18] Kim, J.H., Lee, C., Lee, J. (2018). "Two approaches to Sidorenko's conjecture."
  *Trans. Amer. Math. Soc.* 370, pp. 8515--8552.
* [ArXiv2605] [arXiv:2605.14138](https://arxiv.org/abs/2605.14138)
* [BR65] Blakley, G. R. and Roy, P. (1965). "A Hölder type inequality for symmetric matrices
  with nonnegative entries." *Proc. Amer. Math. Soc.* 16, pp. 1244--1245.
* [OAI26a] OpenAI, *A counterexample to Sidorenko's conjecture*. OpenAI Math Release preprint
  (2026).
  https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Sidorenkos-conjecture-September-23-2026/paper.pdf
-/

section

open Finset SimpleGraph

namespace SidorenkoConjecture

open LimitObjects

/- ## Homomorphism density

We use `SimpleGraph.homCount` / `SimpleGraph.homDensity` from
`FormalConjecturesForMathlib.Combinatorics.SimpleGraph.HomDensity` for finite host graphs,
and `graphonHomDensity` / `graphonEdgeDensity` from
`FormalConjecturesForMathlib.Combinatorics.LimitObjects.Graphon` for graphons on measure spaces. -/

variable {V W : Type*}

/- ## The conjecture -/

/- ## Proved graphon special cases -/

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (W : LimitObjects.Graphon)  :
    (1 ≤ k) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (W : LimitObjects.Graphon)  :
    (1 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) (W : LimitObjects.Graphon)  :
    (1 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (W : LimitObjects.Graphon)  :
    (1 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (W : LimitObjects.Graphon)  :
    (1 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) (W : LimitObjects.Graphon)  :
    (1 ≤ k) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (W : LimitObjects.Graphon)  :
    (1 ≤ k) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((1 ≤ k) ↔ (True))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((1 ≤ k) ↔ (True))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((1 ≤ k) ↔ (True))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((1 ≤ k) ↔ (True))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((1 ≤ k) ↔ (True))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((1 ≤ k) ↔ (True))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (3 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (3 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (3 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (3 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (3 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (3 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (3 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (3 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (3 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (3 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (3 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (3 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (3 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (3 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (3 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 1) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W

set_option maxHeartbeats 200000 in
example (k : ℕ) (W : LimitObjects.Graphon) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) (W : LimitObjects.Graphon) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) (W : LimitObjects.Graphon) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) (W : LimitObjects.Graphon) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) (W : LimitObjects.Graphon) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) (W : LimitObjects.Graphon) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (W : LimitObjects.Graphon) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (W : LimitObjects.Graphon) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) ↔
    (∀ (k : ℕ) (hk : k ≥ 1) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) ↔
    (∀ (k : ℕ) (hk : k ≥ 1) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) ↔
    (∀ (k : ℕ) (hk : k ≥ 1) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) ↔
    (∀ (k : ℕ) (hk : k ≥ 1) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk₀ : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) ↔
    (∀ (k : ℕ) (hk₀ : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) ↔
    (∀ (k : ℕ) (hk₀ : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) ↔
    (∀ (k : ℕ) (hk₀ : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) ↔
    (∀ (k : ℕ) (hk₀ : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : ¬(k < 1)) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W

set_option maxHeartbeats 200000 in
example (k : ℕ) (W : LimitObjects.Graphon) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) (W : LimitObjects.Graphon) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) (W : LimitObjects.Graphon) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) (W : LimitObjects.Graphon) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) (W : LimitObjects.Graphon) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) (W : LimitObjects.Graphon) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (W : LimitObjects.Graphon) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (W : LimitObjects.Graphon) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) ↔
    (∀ (k : ℕ) (hk : ¬(k < 1)) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) ↔
    (∀ (k : ℕ) (hk : ¬(k < 1)) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) ↔
    (∀ (k : ℕ) (hk : ¬(k < 1)) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) ↔
    (∀ (k : ℕ) (hk : ¬(k < 1)) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 0 < k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W

set_option maxHeartbeats 200000 in
example (k : ℕ) (W : LimitObjects.Graphon) :
    (1 ≤ k) ↔ (0 < k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) (W : LimitObjects.Graphon) :
    (1 ≤ k) ↔ (0 < k) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) (W : LimitObjects.Graphon) :
    (1 ≤ k) ↔ (0 < k) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) (W : LimitObjects.Graphon) :
    (1 ≤ k) ↔ (0 < k) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) (W : LimitObjects.Graphon) :
    (1 ≤ k) ↔ (0 < k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) (W : LimitObjects.Graphon) :
    (1 ≤ k) ↔ (0 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (W : LimitObjects.Graphon) :
    (1 ≤ k) ↔ (0 < k) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (W : LimitObjects.Graphon) :
    (1 ≤ k) ↔ (0 < k) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) ↔
    (∀ (k : ℕ) (hk : 0 < k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) ↔
    (∀ (k : ℕ) (hk : 0 < k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) ↔
    (∀ (k : ℕ) (hk : 0 < k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) ↔
    (∀ (k : ℕ) (hk : 0 < k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 1) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (3 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 1) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (3 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 1) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (3 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 1) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (3 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 1) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (3 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 1) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (3 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 1) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (3 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 1) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (3 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : k ≥ 1) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (3 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : k ≥ 1) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (3 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : k ≥ 1) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (3 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : k ≥ 1) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (3 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : k ≥ 1) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (3 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : k ≥ 1) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (3 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : k ≥ 1) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (3 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 0 < k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (3 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (3 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (3 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (3 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (3 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (3 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (3 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (3 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : 0 < k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (3 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : 0 < k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (3 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : 0 < k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (3 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : 0 < k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (3 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : 0 < k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (3 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : 0 < k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (3 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) →
    (∀ (k : ℕ) (hk : 0 < k) (W : LimitObjects.Graphon), (graphonEdgeDensity W) ^ (cycleGraph (3 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (W : LimitObjects.Graphon) (hk : 1 ≤ k) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (k : ℕ) (W : LimitObjects.Graphon) (hk : 1 ≤ k) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (W : LimitObjects.Graphon) (hk : 1 ≤ k) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (k : ℕ) (W : LimitObjects.Graphon) (hk : 1 ≤ k) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (W : LimitObjects.Graphon) (hk : 1 ≤ k) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
