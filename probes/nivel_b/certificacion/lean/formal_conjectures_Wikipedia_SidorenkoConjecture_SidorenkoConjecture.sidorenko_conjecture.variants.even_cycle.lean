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

/- ## Further variants of Sidorenko's conjecture -/

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj]  :
    (2 ≤ k) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj]  :
    (2 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj]  :
    (2 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj]  :
    (2 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj]  :
    (2 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj]  :
    (2 ≤ k) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj]  :
    (2 ≤ k) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (True))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (True))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (True))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (True))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (True))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (True))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 < k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : 2 < k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : 2 < k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : 2 < k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : 2 < k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : 2 < k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : 2 < k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : 2 < k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj]  :
    (2 ≤ k) ↔ (2 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj]  :
    (2 ≤ k) ↔ (2 < k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj]  :
    (2 ≤ k) ↔ (2 < k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj]  :
    (2 ≤ k) ↔ (2 < k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj]  :
    (2 ≤ k) ↔ (2 < k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj]  :
    (2 ≤ k) ↔ (2 < k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj]  :
    (2 ≤ k) ↔ (2 < k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (2 < k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (2 < k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (2 < k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (2 < k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (2 < k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (2 < k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : 3 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : 3 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : 3 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : 3 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : 3 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : 3 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : 3 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj]  :
    (2 ≤ k) ↔ (3 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj]  :
    (2 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj]  :
    (2 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj]  :
    (2 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj]  :
    (2 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj]  :
    (2 ≤ k) ↔ (3 ≤ k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj]  :
    (2 ≤ k) ↔ (3 ≤ k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 2) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj] :
    (2 ≤ k) ↔ (k ≥ 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj] :
    (2 ≤ k) ↔ (k ≥ 2) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj] :
    (2 ≤ k) ↔ (k ≥ 2) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj] :
    (2 ≤ k) ↔ (k ≥ 2) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj] :
    (2 ≤ k) ↔ (k ≥ 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj] :
    (2 ≤ k) ↔ (k ≥ 2) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj] :
    (2 ≤ k) ↔ (k ≥ 2) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj] :
    (2 ≤ k) ↔ (k ≥ 2) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) ↔
    (∀ (k : ℕ) (hk : k ≥ 2) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) ↔
    (∀ (k : ℕ) (hk : k ≥ 2) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) ↔
    (∀ (k : ℕ) (hk : k ≥ 2) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) ↔
    (∀ (k : ℕ) (hk : k ≥ 2) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk₀ : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) ↔
    (∀ (k : ℕ) (hk₀ : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) ↔
    (∀ (k : ℕ) (hk₀ : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) ↔
    (∀ (k : ℕ) (hk₀ : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) ↔
    (∀ (k : ℕ) (hk₀ : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : ¬(k < 2)) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj] :
    (2 ≤ k) ↔ (¬(k < 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj] :
    (2 ≤ k) ↔ (¬(k < 2)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj] :
    (2 ≤ k) ↔ (¬(k < 2)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj] :
    (2 ≤ k) ↔ (¬(k < 2)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj] :
    (2 ≤ k) ↔ (¬(k < 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj] :
    (2 ≤ k) ↔ (¬(k < 2)) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj] :
    (2 ≤ k) ↔ (¬(k < 2)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj] :
    (2 ≤ k) ↔ (¬(k < 2)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) ↔
    (∀ (k : ℕ) (hk : ¬(k < 2)) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) ↔
    (∀ (k : ℕ) (hk : ¬(k < 2)) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) ↔
    (∀ (k : ℕ) (hk : ¬(k < 2)) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) ↔
    (∀ (k : ℕ) (hk : ¬(k < 2)) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 < k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj] :
    (2 ≤ k) ↔ (1 < k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj] :
    (2 ≤ k) ↔ (1 < k) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj] :
    (2 ≤ k) ↔ (1 < k) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj] :
    (2 ≤ k) ↔ (1 < k) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj] :
    (2 ≤ k) ↔ (1 < k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj] :
    (2 ≤ k) ↔ (1 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj] :
    (2 ≤ k) ↔ (1 < k) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj] :
    (2 ≤ k) ↔ (1 < k) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) ↔
    (∀ (k : ℕ) (hk : 1 < k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) ↔
    (∀ (k : ℕ) (hk : 1 < k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) ↔
    (∀ (k : ℕ) (hk : 1 < k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) ↔
    (∀ (k : ℕ) (hk : 1 < k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k > 2) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : k > 2) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : k > 2) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : k > 2) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : k > 2) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : k > 2) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : k > 2) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : k > 2) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj]  :
    (2 ≤ k) ↔ (k > 2) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj]  :
    (2 ≤ k) ↔ (k > 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj]  :
    (2 ≤ k) ↔ (k > 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj]  :
    (2 ≤ k) ↔ (k > 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj]  :
    (2 ≤ k) ↔ (k > 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj]  :
    (2 ≤ k) ↔ (k > 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj]  :
    (2 ≤ k) ↔ (k > 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (k > 2))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (k > 2))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (k > 2))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (k > 2))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (k > 2))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (k > 2))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k > 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k > 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k > 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k > 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k > 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k > 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 3) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : k ≥ 3) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : k ≥ 3) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : k ≥ 3) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : k ≥ 3) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : k ≥ 3) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : k ≥ 3) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : k ≥ 3) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj]  :
    (2 ≤ k) ↔ (k ≥ 3) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj]  :
    (2 ≤ k) ↔ (k ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj]  :
    (2 ≤ k) ↔ (k ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj]  :
    (2 ≤ k) ↔ (k ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj]  :
    (2 ≤ k) ↔ (k ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj]  :
    (2 ≤ k) ↔ (k ≥ 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj]  :
    (2 ≤ k) ↔ (k ≥ 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (k ≥ 3))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (k ≥ 3))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (k ≥ 3))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (k ≥ 3))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (k ≥ 3))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (k ≥ 3))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (k ≥ 3))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k ≥ 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k ≥ 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k ≥ 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k ≥ 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k ≥ 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k ≥ 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k ≥ 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj]  :
    (2 ≤ k) ↔ (1 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj]  :
    (2 ≤ k) ↔ (1 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj]  :
    (2 ≤ k) ↔ (1 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj]  :
    (2 ≤ k) ↔ (1 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj]  :
    (2 ≤ k) ↔ (1 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj]  :
    (2 ≤ k) ↔ (1 ≤ k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj]  :
    (2 ≤ k) ↔ (1 ≤ k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (1 ≤ k))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (1 ≤ k))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (1 ≤ k))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (1 ≤ k))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (1 ≤ k))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (1 ≤ k))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (1 ≤ k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (1 ≤ k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (1 ≤ k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (1 ≤ k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (1 ≤ k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (1 ≤ k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 < k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (3 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 < k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (3 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 < k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (3 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 < k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (3 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 < k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (3 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 < k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (3 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 < k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (3 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 < k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (3 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : 1 < k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (3 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : 1 < k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (3 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : 1 < k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (3 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : 1 < k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (3 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : 1 < k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (3 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : 1 < k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (3 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (2 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) →
    (∀ (k : ℕ) (hk : 1 < k) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj], homDensity (completeGraph (Fin 2)) G ^
        ((cycleGraph (3 * k)).edgeFinset.card) ≤
      homDensity (cycleGraph (2 * k)) G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj] (hk : 2 ≤ k) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj] (hk : 2 ≤ k) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj] (hk : 2 ≤ k) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj] (hk : 2 ≤ k) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W) [DecidableRel G.Adj] (hk : 2 ≤ k) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
