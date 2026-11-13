import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.WellTotallyDominated
/-!
# Written on the Wall II - Conjecture 314

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

section

namespace WrittenOnTheWallII.GraphConjecture314

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The size of a largest induced path of $G$, as a natural number.

A subset $s \subseteq V(G)$ is an *induced path* when the induced subgraph
`G.induce s` is a tree in which every vertex has degree at most $2$
(equivalently: a tree that is itself a path graph). We define
`largestInducedPathSize G` as the supremum of `s.card` over all such subsets.

**Disambiguation.** This is *not* the `SimpleGraph.path` invariant, which is the
floor of the average distance — that one is the wrong tool for WOWII Conjecture
314, where $\mathrm{path}(G)$ denotes the **size of a largest induced path**.

TODO: it would probably be clearer to rename the `SimpleGraph.path` invariant to
something like `pathBound` / `floorAvgDist` to avoid this naming collision. -/
noncomputable def largestInducedPathSize (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  sSup { n | ∃ s : Finset α,
              s.card = n ∧
              (G.induce (s : Set α)).IsTree ∧
              ∀ v : (s : Set α), (G.induce (s : Set α)).degree v ≤ 2 }

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False), IsWellTotallyDominated G) →
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False), IsWellTotallyDominated G) →
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False), IsWellTotallyDominated G) →
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False), IsWellTotallyDominated G) →
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False), IsWellTotallyDominated G) →
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False), IsWellTotallyDominated G) →
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False), IsWellTotallyDominated G) →
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) :
    (largestInducedPathSize G ≤ 4) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) :
    (largestInducedPathSize G ≤ 4) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) :
    (largestInducedPathSize G ≤ 4) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) :
    (largestInducedPathSize G ≤ 4) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) :
    (largestInducedPathSize G ≤ 4) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) :
    (largestInducedPathSize G ≤ 4) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) :
    (largestInducedPathSize G ≤ 4) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G < 4), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) →
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G < 4), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) →
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G < 4), IsWellTotallyDominated G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) →
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G < 4), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) →
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G < 4), IsWellTotallyDominated G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) →
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G < 4), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) →
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G < 4), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) →
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G < 4), IsWellTotallyDominated G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) :
    (largestInducedPathSize G ≤ 4) ↔ (largestInducedPathSize G < 4) := by
  omega

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) :
    (largestInducedPathSize G ≤ 4) ↔ (largestInducedPathSize G < 4) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) :
    (largestInducedPathSize G ≤ 4) ↔ (largestInducedPathSize G < 4) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) :
    (largestInducedPathSize G ≤ 4) ↔ (largestInducedPathSize G < 4) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) :
    (largestInducedPathSize G ≤ 4) ↔ (largestInducedPathSize G < 4) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) :
    (largestInducedPathSize G ≤ 4) ↔ (largestInducedPathSize G < 4) := by
  simp_all

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) :
    (largestInducedPathSize G ≤ 4) ↔ (largestInducedPathSize G < 4) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 5), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 5), IsWellTotallyDominated G) →
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 5), IsWellTotallyDominated G) →
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 5), IsWellTotallyDominated G) →
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 5), IsWellTotallyDominated G) →
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 5), IsWellTotallyDominated G) →
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 5), IsWellTotallyDominated G) →
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 5), IsWellTotallyDominated G) →
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) :
    (largestInducedPathSize G ≤ 4) ↔ (largestInducedPathSize G ≤ 5) := by
  omega

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) :
    (largestInducedPathSize G ≤ 4) ↔ (largestInducedPathSize G ≤ 5) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) :
    (largestInducedPathSize G ≤ 4) ↔ (largestInducedPathSize G ≤ 5) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) :
    (largestInducedPathSize G ≤ 4) ↔ (largestInducedPathSize G ≤ 5) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) :
    (largestInducedPathSize G ≤ 4) ↔ (largestInducedPathSize G ≤ 5) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) :
    (largestInducedPathSize G ≤ 4) ↔ (largestInducedPathSize G ≤ 5) := by
  simp_all

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) :
    (largestInducedPathSize G ≤ 4) ↔ (largestInducedPathSize G ≤ 5) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : 4 ≥ largestInducedPathSize G), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] :
    (largestInducedPathSize G ≤ 4) ↔ (4 ≥ largestInducedPathSize G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] :
    (largestInducedPathSize G ≤ 4) ↔ (4 ≥ largestInducedPathSize G) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] :
    (largestInducedPathSize G ≤ 4) ↔ (4 ≥ largestInducedPathSize G) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] :
    (largestInducedPathSize G ≤ 4) ↔ (4 ≥ largestInducedPathSize G) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] :
    (largestInducedPathSize G ≤ 4) ↔ (4 ≥ largestInducedPathSize G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] :
    (largestInducedPathSize G ≤ 4) ↔ (4 ≥ largestInducedPathSize G) := by
  omega

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] :
    (largestInducedPathSize G ≤ 4) ↔ (4 ≥ largestInducedPathSize G) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] :
    (largestInducedPathSize G ≤ 4) ↔ (4 ≥ largestInducedPathSize G) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) ↔
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : 4 ≥ largestInducedPathSize G), IsWellTotallyDominated G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) ↔
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : 4 ≥ largestInducedPathSize G), IsWellTotallyDominated G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) ↔
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : 4 ≥ largestInducedPathSize G), IsWellTotallyDominated G) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) ↔
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : 4 ≥ largestInducedPathSize G), IsWellTotallyDominated G) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hG : G.Connected) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) ↔
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hG : G.Connected) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) ↔
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hG : G.Connected) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) ↔
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hG : G.Connected) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) ↔
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hG : G.Connected) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG₀ : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) ↔
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG₀ : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) ↔
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG₀ : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) ↔
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG₀ : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) ↔
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG₀ : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : 4 > largestInducedPathSize G), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) →
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : 4 > largestInducedPathSize G), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) →
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : 4 > largestInducedPathSize G), IsWellTotallyDominated G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) →
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : 4 > largestInducedPathSize G), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) →
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : 4 > largestInducedPathSize G), IsWellTotallyDominated G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) →
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : 4 > largestInducedPathSize G), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) →
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : 4 > largestInducedPathSize G), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) →
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : 4 > largestInducedPathSize G), IsWellTotallyDominated G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) :
    (largestInducedPathSize G ≤ 4) ↔ (4 > largestInducedPathSize G) := by
  omega

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) :
    (largestInducedPathSize G ≤ 4) ↔ (4 > largestInducedPathSize G) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) :
    (largestInducedPathSize G ≤ 4) ↔ (4 > largestInducedPathSize G) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) :
    (largestInducedPathSize G ≤ 4) ↔ (4 > largestInducedPathSize G) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) :
    (largestInducedPathSize G ≤ 4) ↔ (4 > largestInducedPathSize G) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) :
    (largestInducedPathSize G ≤ 4) ↔ (4 > largestInducedPathSize G) := by
  simp_all

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) :
    (largestInducedPathSize G ≤ 4) ↔ (4 > largestInducedPathSize G) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : 5 ≥ largestInducedPathSize G), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : 5 ≥ largestInducedPathSize G), IsWellTotallyDominated G) →
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : 5 ≥ largestInducedPathSize G), IsWellTotallyDominated G) →
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : 5 ≥ largestInducedPathSize G), IsWellTotallyDominated G) →
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : 5 ≥ largestInducedPathSize G), IsWellTotallyDominated G) →
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : 5 ≥ largestInducedPathSize G), IsWellTotallyDominated G) →
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : 5 ≥ largestInducedPathSize G), IsWellTotallyDominated G) →
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : 5 ≥ largestInducedPathSize G), IsWellTotallyDominated G) →
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) :
    (largestInducedPathSize G ≤ 4) ↔ (5 ≥ largestInducedPathSize G) := by
  omega

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) :
    (largestInducedPathSize G ≤ 4) ↔ (5 ≥ largestInducedPathSize G) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) :
    (largestInducedPathSize G ≤ 4) ↔ (5 ≥ largestInducedPathSize G) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) :
    (largestInducedPathSize G ≤ 4) ↔ (5 ≥ largestInducedPathSize G) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) :
    (largestInducedPathSize G ≤ 4) ↔ (5 ≥ largestInducedPathSize G) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) :
    (largestInducedPathSize G ≤ 4) ↔ (5 ≥ largestInducedPathSize G) := by
  simp_all

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) :
    (largestInducedPathSize G ≤ 4) ↔ (5 ≥ largestInducedPathSize G) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hG : G.Connected), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hG : G.Connected), IsWellTotallyDominated G) →
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hG : G.Connected), IsWellTotallyDominated G) →
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hG : G.Connected), IsWellTotallyDominated G) →
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hG : G.Connected), IsWellTotallyDominated G) →
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hG : G.Connected), IsWellTotallyDominated G) →
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hG : G.Connected), IsWellTotallyDominated G) →
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hG : G.Connected), IsWellTotallyDominated G) →
    (∀ [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4), IsWellTotallyDominated G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) :
    (largestInducedPathSize G ≤ 4) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) :
    (largestInducedPathSize G ≤ 4) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) :
    (largestInducedPathSize G ≤ 4) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) :
    (largestInducedPathSize G ≤ 4) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) :
    (largestInducedPathSize G ≤ 4) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) :
    (largestInducedPathSize G ≤ 4) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) :
    (largestInducedPathSize G ≤ 4) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False) (hPath : largestInducedPathSize G ≤ 4) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
