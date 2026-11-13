import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 742

*References:*
- [erdosproblems.com/742](https://www.erdosproblems.com/742)
- [Pl75] Plesník, Ján, Critical graphs of given diameter. Acta Fac. Rerum Natur. Univ. Comenian.
  Math. 30 (1975), 71-93.
- [CaHa79] Caccetta, L. and Häggkvist, R., On diameter critical graphs.
  Discrete Math. 28 (1979), 223-229.
- [Fa87] Fan, Genghua, On diameter 2-critical graphs. Discrete Math. 67 (1987), 235-240.
- [Fü92] Füredi, Zoltán, The maximum number of edges in a minimal graph of diameter 2.
  J. Graph Theory 16 (1992), 81-98.
-/

section

open SimpleGraph

namespace Erdos742

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A graph is diameter-2-critical if it has diameter $2$ and removing any edge
increases the diameter beyond $2$. -/
def IsDiameter2Critical (G : SimpleGraph V) : Prop :=
  G.diam = 2 ∧ ∀ e ∈ G.edgeSet, (G.deleteEdges {e}).diam ≠ 2

namespace variants

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V < 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) →
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V < 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) →
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V < 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) →
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V < 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) →
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V < 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) →
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V < 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) →
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V < 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) →
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V < 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsDiameter2Critical G) :
    (Fintype.card V ≤ 24 ∨ Fintype.card V = 26) ↔ (Fintype.card V < 24 ∨ Fintype.card V = 26) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsDiameter2Critical G) :
    (Fintype.card V ≤ 24 ∨ Fintype.card V = 26) ↔ (Fintype.card V < 24 ∨ Fintype.card V = 26) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsDiameter2Critical G) :
    (Fintype.card V ≤ 24 ∨ Fintype.card V = 26) ↔ (Fintype.card V < 24 ∨ Fintype.card V = 26) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsDiameter2Critical G) :
    (Fintype.card V ≤ 24 ∨ Fintype.card V = 26) ↔ (Fintype.card V < 24 ∨ Fintype.card V = 26) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsDiameter2Critical G) :
    (Fintype.card V ≤ 24 ∨ Fintype.card V = 26) ↔ (Fintype.card V < 24 ∨ Fintype.card V = 26) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsDiameter2Critical G) :
    (Fintype.card V ≤ 24 ∨ Fintype.card V = 26) ↔ (Fintype.card V < 24 ∨ Fintype.card V = 26) := by
  simp_all

set_option maxHeartbeats 200000 in
example (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsDiameter2Critical G) :
    (Fintype.card V ≤ 24 ∨ Fintype.card V = 26) ↔ (Fintype.card V < 24 ∨ Fintype.card V = 26) := by
  plausible

set_option maxHeartbeats 200000 in
example : ¬((Fintype.card V ≤ 24 ∨ Fintype.card V = 26) ↔ (Fintype.card V < 24 ∨ Fintype.card V = 26)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((Fintype.card V ≤ 24 ∨ Fintype.card V = 26) ↔ (Fintype.card V < 24 ∨ Fintype.card V = 26)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 25 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 25 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) →
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 25 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) →
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 25 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) →
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 25 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) →
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 25 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) →
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 25 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) →
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 25 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) →
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) →
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 25 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) →
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 25 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) →
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 25 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) →
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 25 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) →
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 25 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) →
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 25 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) →
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 25 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsDiameter2Critical G) :
    (Fintype.card V ≤ 24 ∨ Fintype.card V = 26) ↔ (Fintype.card V ≤ 25 ∨ Fintype.card V = 26) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsDiameter2Critical G) :
    (Fintype.card V ≤ 24 ∨ Fintype.card V = 26) ↔ (Fintype.card V ≤ 25 ∨ Fintype.card V = 26) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsDiameter2Critical G) :
    (Fintype.card V ≤ 24 ∨ Fintype.card V = 26) ↔ (Fintype.card V ≤ 25 ∨ Fintype.card V = 26) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsDiameter2Critical G) :
    (Fintype.card V ≤ 24 ∨ Fintype.card V = 26) ↔ (Fintype.card V ≤ 25 ∨ Fintype.card V = 26) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsDiameter2Critical G) :
    (Fintype.card V ≤ 24 ∨ Fintype.card V = 26) ↔ (Fintype.card V ≤ 25 ∨ Fintype.card V = 26) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsDiameter2Critical G) :
    (Fintype.card V ≤ 24 ∨ Fintype.card V = 26) ↔ (Fintype.card V ≤ 25 ∨ Fintype.card V = 26) := by
  simp_all

set_option maxHeartbeats 200000 in
example (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsDiameter2Critical G) :
    (Fintype.card V ≤ 24 ∨ Fintype.card V = 26) ↔ (Fintype.card V ≤ 25 ∨ Fintype.card V = 26) := by
  plausible

set_option maxHeartbeats 200000 in
example : ¬((Fintype.card V ≤ 24 ∨ Fintype.card V = 26) ↔ (Fintype.card V ≤ 25 ∨ Fintype.card V = 26)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((Fintype.card V ≤ 24 ∨ Fintype.card V = 26) ↔ (Fintype.card V ≤ 25 ∨ Fintype.card V = 26)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), (Fintype.card V) ^ 2 / 4 ≥ G.edgeFinset.card

set_option maxHeartbeats 200000 in
example (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) ↔ ((Fintype.card V) ^ 2 / 4 ≥ G.edgeFinset.card) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) ↔ ((Fintype.card V) ^ 2 / 4 ≥ G.edgeFinset.card) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) ↔ ((Fintype.card V) ^ 2 / 4 ≥ G.edgeFinset.card) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) ↔ ((Fintype.card V) ^ 2 / 4 ≥ G.edgeFinset.card) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) ↔ ((Fintype.card V) ^ 2 / 4 ≥ G.edgeFinset.card) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) ↔ ((Fintype.card V) ^ 2 / 4 ≥ G.edgeFinset.card) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) ↔ ((Fintype.card V) ^ 2 / 4 ≥ G.edgeFinset.card) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) ↔ ((Fintype.card V) ^ 2 / 4 ≥ G.edgeFinset.card) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) ↔
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), (Fintype.card V) ^ 2 / 4 ≥ G.edgeFinset.card) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) ↔
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), (Fintype.card V) ^ 2 / 4 ≥ G.edgeFinset.card) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) ↔
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), (Fintype.card V) ^ 2 / 4 ≥ G.edgeFinset.card) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) ↔
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), (Fintype.card V) ^ 2 / 4 ≥ G.edgeFinset.card) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsDiameter2Critical G) (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) ↔
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsDiameter2Critical G) (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) ↔
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsDiameter2Critical G) (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) ↔
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsDiameter2Critical G) (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) ↔
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsDiameter2Critical G) (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn₀ : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) ↔
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn₀ : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) ↔
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn₀ : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) ↔
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn₀ : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) ↔
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn₀ : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V < 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), (Fintype.card V) ^ 2 / 4 ≥ G.edgeFinset.card

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) →
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V < 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), (Fintype.card V) ^ 2 / 4 ≥ G.edgeFinset.card) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) →
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V < 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), (Fintype.card V) ^ 2 / 4 ≥ G.edgeFinset.card) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) →
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V < 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), (Fintype.card V) ^ 2 / 4 ≥ G.edgeFinset.card) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) →
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V < 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), (Fintype.card V) ^ 2 / 4 ≥ G.edgeFinset.card) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) →
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V < 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), (Fintype.card V) ^ 2 / 4 ≥ G.edgeFinset.card) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) →
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V < 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), (Fintype.card V) ^ 2 / 4 ≥ G.edgeFinset.card) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) →
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V < 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), (Fintype.card V) ^ 2 / 4 ≥ G.edgeFinset.card) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsDiameter2Critical G) :
    (Fintype.card V ≤ 24 ∨ Fintype.card V = 26) ↔ (Fintype.card V < 24 ∨ Fintype.card V = 26) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsDiameter2Critical G) :
    (Fintype.card V ≤ 24 ∨ Fintype.card V = 26) ↔ (Fintype.card V < 24 ∨ Fintype.card V = 26) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsDiameter2Critical G) :
    (Fintype.card V ≤ 24 ∨ Fintype.card V = 26) ↔ (Fintype.card V < 24 ∨ Fintype.card V = 26) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsDiameter2Critical G) :
    (Fintype.card V ≤ 24 ∨ Fintype.card V = 26) ↔ (Fintype.card V < 24 ∨ Fintype.card V = 26) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsDiameter2Critical G) :
    (Fintype.card V ≤ 24 ∨ Fintype.card V = 26) ↔ (Fintype.card V < 24 ∨ Fintype.card V = 26) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsDiameter2Critical G) :
    (Fintype.card V ≤ 24 ∨ Fintype.card V = 26) ↔ (Fintype.card V < 24 ∨ Fintype.card V = 26) := by
  simp_all

set_option maxHeartbeats 200000 in
example (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsDiameter2Critical G) :
    (Fintype.card V ≤ 24 ∨ Fintype.card V = 26) ↔ (Fintype.card V < 24 ∨ Fintype.card V = 26) := by
  plausible

set_option maxHeartbeats 200000 in
example : ¬((Fintype.card V ≤ 24 ∨ Fintype.card V = 26) ↔ (Fintype.card V < 24 ∨ Fintype.card V = 26)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((Fintype.card V ≤ 24 ∨ Fintype.card V = 26) ↔ (Fintype.card V < 24 ∨ Fintype.card V = 26)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 25 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), (Fintype.card V) ^ 2 / 4 ≥ G.edgeFinset.card

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 25 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), (Fintype.card V) ^ 2 / 4 ≥ G.edgeFinset.card) →
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 25 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), (Fintype.card V) ^ 2 / 4 ≥ G.edgeFinset.card) →
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 25 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), (Fintype.card V) ^ 2 / 4 ≥ G.edgeFinset.card) →
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 25 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), (Fintype.card V) ^ 2 / 4 ≥ G.edgeFinset.card) →
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 25 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), (Fintype.card V) ^ 2 / 4 ≥ G.edgeFinset.card) →
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 25 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), (Fintype.card V) ^ 2 / 4 ≥ G.edgeFinset.card) →
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 25 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), (Fintype.card V) ^ 2 / 4 ≥ G.edgeFinset.card) →
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) →
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 25 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), (Fintype.card V) ^ 2 / 4 ≥ G.edgeFinset.card) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) →
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 25 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), (Fintype.card V) ^ 2 / 4 ≥ G.edgeFinset.card) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) →
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 25 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), (Fintype.card V) ^ 2 / 4 ≥ G.edgeFinset.card) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) →
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 25 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), (Fintype.card V) ^ 2 / 4 ≥ G.edgeFinset.card) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) →
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 25 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), (Fintype.card V) ^ 2 / 4 ≥ G.edgeFinset.card) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) →
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 25 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), (Fintype.card V) ^ 2 / 4 ≥ G.edgeFinset.card) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4) →
    (∀ (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 25 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G), (Fintype.card V) ^ 2 / 4 ≥ G.edgeFinset.card) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsDiameter2Critical G) :
    (Fintype.card V ≤ 24 ∨ Fintype.card V = 26) ↔ (Fintype.card V ≤ 25 ∨ Fintype.card V = 26) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsDiameter2Critical G) :
    (Fintype.card V ≤ 24 ∨ Fintype.card V = 26) ↔ (Fintype.card V ≤ 25 ∨ Fintype.card V = 26) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsDiameter2Critical G) :
    (Fintype.card V ≤ 24 ∨ Fintype.card V = 26) ↔ (Fintype.card V ≤ 25 ∨ Fintype.card V = 26) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsDiameter2Critical G) :
    (Fintype.card V ≤ 24 ∨ Fintype.card V = 26) ↔ (Fintype.card V ≤ 25 ∨ Fintype.card V = 26) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsDiameter2Critical G) :
    (Fintype.card V ≤ 24 ∨ Fintype.card V = 26) ↔ (Fintype.card V ≤ 25 ∨ Fintype.card V = 26) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsDiameter2Critical G) :
    (Fintype.card V ≤ 24 ∨ Fintype.card V = 26) ↔ (Fintype.card V ≤ 25 ∨ Fintype.card V = 26) := by
  simp_all

set_option maxHeartbeats 200000 in
example (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsDiameter2Critical G) :
    (Fintype.card V ≤ 24 ∨ Fintype.card V = 26) ↔ (Fintype.card V ≤ 25 ∨ Fintype.card V = 26) := by
  plausible

set_option maxHeartbeats 200000 in
example : ¬((Fintype.card V ≤ 24 ∨ Fintype.card V = 26) ↔ (Fintype.card V ≤ 25 ∨ Fintype.card V = 26)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((Fintype.card V ≤ 24 ∨ Fintype.card V = 26) ↔ (Fintype.card V ≤ 25 ∨ Fintype.card V = 26)) :=
  by decide

set_option maxHeartbeats 200000 in
example (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
