import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Combinatorics.Digraph.Tournament
--   import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.HomDensity
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

/- ## Tournament Anti-Sidorenko (TAS) Trees Conjecture -/

open scoped Classical in
/--
**The $(2,3,4)$-spider tree.**
A tree composed of three paths of lengths 2, 3, and 4 joined at a single central vertex: the
centre is the unique vertex of degree 3 (every other vertex has degree at most 2), so the tree
has exactly three leaves, at distances 2, 3 and 4 from the centre.
-/
def IsSpider234 {V : Type*} [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj] : Prop :=
  T.IsTree ∧ Fintype.card V = 10 ∧
  ∃ (center l₁ l₂ l₃ : V),
    T.degree center = 3 ∧
    (∀ v, v ≠ center → T.degree v ≤ 2) ∧
    l₁ ≠ l₂ ∧ l₁ ≠ l₃ ∧ l₂ ≠ l₃ ∧
    T.degree l₁ = 1 ∧ T.degree l₂ = 1 ∧ T.degree l₃ = 1 ∧
    ({T.dist center l₁, T.dist center l₂, T.dist center l₃} : Multiset ℕ) = {2, 3, 4}

/- ## Proved special cases -/

/- ## Sidorenko for `K_{2,2}`: auxiliary lemmas -/

/- ## Sidorenko for trees: auxiliary lemmas -/

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) < homDensity H G

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) < homDensity H G) →
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) < homDensity H G) →
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) < homDensity H G) →
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) < homDensity H G) →
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) < homDensity H G) →
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) < homDensity H G) →
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) < homDensity H G) →
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≥ homDensity H G

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≥ homDensity H G) →
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≥ homDensity H G) →
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≥ homDensity H G) →
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≥ homDensity H G) →
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≥ homDensity H G) →
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≥ homDensity H G) →
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≥ homDensity H G) →
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) →
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≥ homDensity H G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) →
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≥ homDensity H G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) →
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≥ homDensity H G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) →
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≥ homDensity H G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) →
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≥ homDensity H G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) →
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≥ homDensity H G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) →
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≥ homDensity H G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity H G ≥ homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card)

set_option maxHeartbeats 200000 in
example {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj] :
    (homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) ↔ (homDensity H G ≥ homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj] :
    (homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) ↔ (homDensity H G ≥ homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj] :
    (homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) ↔ (homDensity H G ≥ homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj] :
    (homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) ↔ (homDensity H G ≥ homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj] :
    (homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) ↔ (homDensity H G ≥ homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj] :
    (homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) ↔ (homDensity H G ≥ homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card)) := by
  omega

set_option maxHeartbeats 200000 in
example {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj] :
    (homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) ↔ (homDensity H G ≥ homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj] :
    (homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) ↔ (homDensity H G ≥ homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) ↔
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity H G ≥ homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) ↔
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity H G ≥ homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) ↔
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity H G ≥ homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) ↔
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity H G ≥ homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H₀ : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H₀.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H₀.edgeFinset.card) ≤ homDensity H₀ G

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) ↔
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H₀ : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H₀.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H₀.edgeFinset.card) ≤ homDensity H₀ G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) ↔
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H₀ : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H₀.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H₀.edgeFinset.card) ≤ homDensity H₀ G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) ↔
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H₀ : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H₀.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H₀.edgeFinset.card) ≤ homDensity H₀ G) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) ↔
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H₀ : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H₀.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H₀.edgeFinset.card) ≤ homDensity H₀ G) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity H G > homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card)

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity H G > homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card)) →
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity H G > homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card)) →
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity H G > homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card)) →
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity H G > homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card)) →
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity H G > homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card)) →
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity H G > homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card)) →
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity H G > homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card)) →
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity H G ≤ homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card)

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity H G ≤ homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card)) →
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity H G ≤ homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card)) →
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity H G ≤ homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card)) →
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity H G ≤ homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card)) →
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity H G ≤ homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card)) →
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity H G ≤ homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card)) →
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity H G ≤ homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card)) →
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) →
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity H G ≤ homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) →
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity H G ≤ homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) →
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity H G ≤ homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) →
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity H G ≤ homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) →
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity H G ≤ homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) →
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity H G ≤ homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G) →
    (∀ {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj], homDensity H G ≤ homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj] (H : SimpleGraph V) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj] (H : SimpleGraph V) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj] (H : SimpleGraph V) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj] (H : SimpleGraph V) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {V W : Type} [Fintype V] [Fintype W] [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj] (H : SimpleGraph V) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
