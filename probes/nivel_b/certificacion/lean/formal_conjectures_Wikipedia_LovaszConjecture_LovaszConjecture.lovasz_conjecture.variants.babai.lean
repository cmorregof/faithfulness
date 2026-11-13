import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Lovász's conjecture on Hamiltonian paths in vertex-transitive graphs (1970)

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Lov%C3%A1sz_conjecture)
* [Lo70] Lovász, L. (1970). Problem 11, in *Combinatorial Structures and their Applications*
  (Proc. Calgary Internat. Conf. 1969), Gordon and Breach, p. 497.
* [Ba79] Babai, L. (1979). "Long cycles in vertex-transitive graphs." *J. Graph Theory* 3,
  pp. 301--304.
* [CHM14] Christofides, D., Hladký, J. and Máthé, A. (2014). "Hamilton cycles in dense
  vertex-transitive graphs." *J. Combin. Theory Ser. B* 109, pp. 34--72.
  [arXiv:1008.2193](https://arxiv.org/abs/1008.2193)
* [KM09] Kutnar, K. and Marušič, D. (2009). "Hamilton cycles and paths in vertex-transitive
  graphs — current directions." *Discrete Math.* 309, pp. 5491--5500.
-/

section

open SimpleGraph

namespace LovaszConjecture

variable {V : Type*}

/-- A graph is **vertex-transitive** if its automorphism group acts transitively on the
vertices: any vertex can be mapped to any other by a graph automorphism. -/
def IsVertexTransitive (G : SimpleGraph V) : Prop :=
  ∀ u v : V, ∃ φ : G ≃g G, φ u = v

/-- `G` has a **Hamiltonian path**: a walk visiting every vertex exactly once. -/
def HasHamiltonianPath [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∃ (a b : V) (p : G.Walk a b), p.IsHamiltonian

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) :
    (3 ≤ Fintype.card V) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) :
    (3 ≤ Fintype.card V) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) :
    (3 ≤ Fintype.card V) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) :
    (3 ≤ Fintype.card V) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) :
    (3 ≤ Fintype.card V) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) :
    (3 ≤ Fintype.card V) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) :
    (3 ≤ Fintype.card V) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) < (c.length : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) < (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) < (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) < (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) < (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) < (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) < (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) < (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 < Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 < Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 < Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 < Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 < Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 < Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 < Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 < Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) :
    (3 ≤ Fintype.card V) ↔ (3 < Fintype.card V) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) :
    (3 ≤ Fintype.card V) ↔ (3 < Fintype.card V) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) :
    (3 ≤ Fintype.card V) ↔ (3 < Fintype.card V) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) :
    (3 ≤ Fintype.card V) ↔ (3 < Fintype.card V) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) :
    (3 ≤ Fintype.card V) ↔ (3 < Fintype.card V) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) :
    (3 ≤ Fintype.card V) ↔ (3 < Fintype.card V) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) :
    (3 ≤ Fintype.card V) ↔ (3 < Fintype.card V) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 4 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 4 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 4 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 4 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 4 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 4 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 4 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 4 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) :
    (3 ≤ Fintype.card V) ↔ (4 ≤ Fintype.card V) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) :
    (3 ≤ Fintype.card V) ↔ (4 ≤ Fintype.card V) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) :
    (3 ≤ Fintype.card V) ↔ (4 ≤ Fintype.card V) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) :
    (3 ≤ Fintype.card V) ↔ (4 ≤ Fintype.card V) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) :
    (3 ≤ Fintype.card V) ↔ (4 ≤ Fintype.card V) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) :
    (3 ≤ Fintype.card V) ↔ (4 ≤ Fintype.card V) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) :
    (3 ≤ Fintype.card V) ↔ (4 ≤ Fintype.card V) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≥ (c.length : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≥ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≥ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≥ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≥ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≥ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≥ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≥ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≥ (c.length : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≥ (c.length : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≥ (c.length : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≥ (c.length : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≥ (c.length : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≥ (c.length : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≥ (c.length : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : Fintype.card V ≥ 3), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (3 ≤ Fintype.card V) ↔ (Fintype.card V ≥ 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (3 ≤ Fintype.card V) ↔ (Fintype.card V ≥ 3) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (3 ≤ Fintype.card V) ↔ (Fintype.card V ≥ 3) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (3 ≤ Fintype.card V) ↔ (Fintype.card V ≥ 3) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (3 ≤ Fintype.card V) ↔ (Fintype.card V ≥ 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (3 ≤ Fintype.card V) ↔ (Fintype.card V ≥ 3) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (3 ≤ Fintype.card V) ↔ (Fintype.card V ≥ 3) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (3 ≤ Fintype.card V) ↔ (Fintype.card V ≥ 3) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : Fintype.card V ≥ 3), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : Fintype.card V ≥ 3), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : Fintype.card V ≥ 3), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : Fintype.card V ≥ 3), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (htrans : IsVertexTransitive G) (hconn : G.Connected) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (htrans : IsVertexTransitive G) (hconn : G.Connected) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (htrans : IsVertexTransitive G) (hconn : G.Connected) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (htrans : IsVertexTransitive G) (hconn : G.Connected) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (htrans : IsVertexTransitive G) (hconn : G.Connected) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn₀ : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn₀ : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn₀ : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn₀ : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn₀ : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : Fintype.card V ≥ 3), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) < (c.length : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : Fintype.card V ≥ 3), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) < (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : Fintype.card V ≥ 3), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) < (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : Fintype.card V ≥ 3), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) < (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : Fintype.card V ≥ 3), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) < (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : Fintype.card V ≥ 3), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) < (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : Fintype.card V ≥ 3), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) < (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : Fintype.card V ≥ 3), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) < (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : Fintype.card V > 3), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : Fintype.card V > 3), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : Fintype.card V > 3), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : Fintype.card V > 3), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : Fintype.card V > 3), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : Fintype.card V > 3), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : Fintype.card V > 3), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : Fintype.card V > 3), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) :
    (3 ≤ Fintype.card V) ↔ (Fintype.card V > 3) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) :
    (3 ≤ Fintype.card V) ↔ (Fintype.card V > 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) :
    (3 ≤ Fintype.card V) ↔ (Fintype.card V > 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) :
    (3 ≤ Fintype.card V) ↔ (Fintype.card V > 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) :
    (3 ≤ Fintype.card V) ↔ (Fintype.card V > 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) :
    (3 ≤ Fintype.card V) ↔ (Fintype.card V > 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) :
    (3 ≤ Fintype.card V) ↔ (Fintype.card V > 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : Fintype.card V ≥ 4), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : Fintype.card V ≥ 4), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : Fintype.card V ≥ 4), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : Fintype.card V ≥ 4), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : Fintype.card V ≥ 4), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : Fintype.card V ≥ 4), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : Fintype.card V ≥ 4), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : Fintype.card V ≥ 4), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) :
    (3 ≤ Fintype.card V) ↔ (Fintype.card V ≥ 4) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) :
    (3 ≤ Fintype.card V) ↔ (Fintype.card V ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) :
    (3 ≤ Fintype.card V) ↔ (Fintype.card V ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) :
    (3 ≤ Fintype.card V) ↔ (Fintype.card V ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) :
    (3 ≤ Fintype.card V) ↔ (Fintype.card V ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) :
    (3 ≤ Fintype.card V) ↔ (Fintype.card V ≥ 4) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) :
    (3 ≤ Fintype.card V) ↔ (Fintype.card V ≥ 4) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : Fintype.card V ≥ 3), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≥ (c.length : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : Fintype.card V ≥ 3), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≥ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : Fintype.card V ≥ 3), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≥ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : Fintype.card V ≥ 3), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≥ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : Fintype.card V ≥ 3), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≥ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : Fintype.card V ≥ 3), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≥ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : Fintype.card V ≥ 3), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≥ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : Fintype.card V ≥ 3), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≥ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : Fintype.card V ≥ 3), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≥ (c.length : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : Fintype.card V ≥ 3), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≥ (c.length : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : Fintype.card V ≥ 3), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≥ (c.length : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : Fintype.card V ≥ 3), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≥ (c.length : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : Fintype.card V ≥ 3), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≥ (c.length : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : Fintype.card V ≥ 3), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≥ (c.length : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : Fintype.card V ≥ 3), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≥ (c.length : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (htrans : IsVertexTransitive G) (hconn : G.Connected), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (htrans : IsVertexTransitive G) (hconn : G.Connected), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (htrans : IsVertexTransitive G) (hconn : G.Connected), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (htrans : IsVertexTransitive G) (hconn : G.Connected), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (htrans : IsVertexTransitive G) (hconn : G.Connected), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (htrans : IsVertexTransitive G) (hconn : G.Connected), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (htrans : IsVertexTransitive G) (hconn : G.Connected), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (htrans : IsVertexTransitive G) (hconn : G.Connected), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V), ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) :
    (3 ≤ Fintype.card V) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) :
    (3 ≤ Fintype.card V) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) :
    (3 ≤ Fintype.card V) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) :
    (3 ≤ Fintype.card V) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) :
    (3 ≤ Fintype.card V) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) :
    (3 ≤ Fintype.card V) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) :
    (3 ≤ Fintype.card V) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
