import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# The reconstruction conjecture

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Reconstruction_conjecture)
* [Ke57] Kelly, P. J. (1957). "A congruence theorem for trees." *Pacific J. Math.* 7,
  pp. 961--968.
* [Ul60] Ulam, S. M. (1960). *A Collection of Mathematical Problems.* Interscience, New York.
* [Ha64] Harary, F. (1964). "On the reconstruction of a graph from a collection of subgraphs."
  In *Theory of Graphs and its Applications*, Academia, Prague, pp. 47--52.
* [Lo72] Lovász, L. (1972). "A note on the line reconstruction problem." *J. Combin. Theory
  Ser. B* 13, pp. 309--310.
* [Mu77] Müller, V. (1977). "The edge reconstruction hypothesis is true for graphs with more
  than n·log n edges." *J. Combin. Theory Ser. B* 22, pp. 281--283.
* [Bo91] Bondy, J. A. (1991). "A graph reconstructor's manual." In *Surveys in Combinatorics*,
  LMS Lecture Note Series 166, Cambridge University Press, pp. 221--252.
-/

section

namespace ReconstructionConjecture

variable {V W : Type*}

/-- Two graphs are **hypomorphic** if there is a bijection `σ` between their vertex sets such
that the vertex-deleted subgraphs `G - v` and `H - σ v` are isomorphic for every vertex `v`;
i.e. `G` and `H` have the same deck of vertex-deleted subgraphs. -/
def Hypomorphic (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ σ : V ≃ W, ∀ v : V, Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ)

/-- Two graphs are **edge-hypomorphic** if there is a bijection `σ` between their edge sets
such that the edge-deleted subgraphs `G - e` and `H - σ e` are isomorphic for every edge `e`;
i.e. `G` and `H` have the same deck of edge-deleted subgraphs. -/
def EdgeHypomorphic (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ σ : G.edgeSet ≃ H.edgeSet, ∀ e : G.edgeSet,
    Nonempty (G.deleteEdges {(e : Sym2 V)} ≃g H.deleteEdges {((σ e : H.edgeSet) : Sym2 W)})

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) ≤ 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) ≤ 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) ≤ 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) ≤ 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) ≤ 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) ≤ 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) ≤ 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) ≤ 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (Nat.factorial (Fintype.card V) ≤ 2 ^ (G.edgeSet.ncard - 1)) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (Nat.factorial (Fintype.card V) ≤ 2 ^ (G.edgeSet.ncard - 1)) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (Nat.factorial (Fintype.card V) ≤ 2 ^ (G.edgeSet.ncard - 1)) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (Nat.factorial (Fintype.card V) ≤ 2 ^ (G.edgeSet.ncard - 1)) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (Nat.factorial (Fintype.card V) ≤ 2 ^ (G.edgeSet.ncard - 1)) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (Nat.factorial (Fintype.card V) ≤ 2 ^ (G.edgeSet.ncard - 1)) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (Nat.factorial (Fintype.card V) ≤ 2 ^ (G.edgeSet.ncard - 1)) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 3 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 3 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 3 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 3 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 3 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 3 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 3 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 3 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 3 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 3 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 3 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 3 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 3 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 3 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 3 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (Nat.factorial (Fintype.card V) < 3 ^ (G.edgeSet.ncard - 1)) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (Nat.factorial (Fintype.card V) < 3 ^ (G.edgeSet.ncard - 1)) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (Nat.factorial (Fintype.card V) < 3 ^ (G.edgeSet.ncard - 1)) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (Nat.factorial (Fintype.card V) < 3 ^ (G.edgeSet.ncard - 1)) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (Nat.factorial (Fintype.card V) < 3 ^ (G.edgeSet.ncard - 1)) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (Nat.factorial (Fintype.card V) < 3 ^ (G.edgeSet.ncard - 1)) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (Nat.factorial (Fintype.card V) < 3 ^ (G.edgeSet.ncard - 1)) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : 2 ^ (G.edgeSet.ncard - 1) > Nat.factorial (Fintype.card V)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (2 ^ (G.edgeSet.ncard - 1) > Nat.factorial (Fintype.card V)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (2 ^ (G.edgeSet.ncard - 1) > Nat.factorial (Fintype.card V)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (2 ^ (G.edgeSet.ncard - 1) > Nat.factorial (Fintype.card V)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (2 ^ (G.edgeSet.ncard - 1) > Nat.factorial (Fintype.card V)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (2 ^ (G.edgeSet.ncard - 1) > Nat.factorial (Fintype.card V)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (2 ^ (G.edgeSet.ncard - 1) > Nat.factorial (Fintype.card V)) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (2 ^ (G.edgeSet.ncard - 1) > Nat.factorial (Fintype.card V)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (2 ^ (G.edgeSet.ncard - 1) > Nat.factorial (Fintype.card V)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) ↔
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : 2 ^ (G.edgeSet.ncard - 1) > Nat.factorial (Fintype.card V)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) ↔
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : 2 ^ (G.edgeSet.ncard - 1) > Nat.factorial (Fintype.card V)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) ↔
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : 2 ^ (G.edgeSet.ncard - 1) > Nat.factorial (Fintype.card V)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) ↔
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : 2 ^ (G.edgeSet.ncard - 1) > Nat.factorial (Fintype.card V)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)), Nonempty (G ≃g H)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) ↔
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)), Nonempty (G ≃g H)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) ↔
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)), Nonempty (G ≃g H)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) ↔
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)), Nonempty (G ≃g H)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) ↔
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)), Nonempty (G ≃g H)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE₀ : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) ↔
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE₀ : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) ↔
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE₀ : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) ↔
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE₀ : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) ↔
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE₀ : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : 2 ^ (G.edgeSet.ncard - 1) ≥ Nat.factorial (Fintype.card V)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : 2 ^ (G.edgeSet.ncard - 1) ≥ Nat.factorial (Fintype.card V)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : 2 ^ (G.edgeSet.ncard - 1) ≥ Nat.factorial (Fintype.card V)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : 2 ^ (G.edgeSet.ncard - 1) ≥ Nat.factorial (Fintype.card V)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : 2 ^ (G.edgeSet.ncard - 1) ≥ Nat.factorial (Fintype.card V)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : 2 ^ (G.edgeSet.ncard - 1) ≥ Nat.factorial (Fintype.card V)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : 2 ^ (G.edgeSet.ncard - 1) ≥ Nat.factorial (Fintype.card V)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : 2 ^ (G.edgeSet.ncard - 1) ≥ Nat.factorial (Fintype.card V)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (2 ^ (G.edgeSet.ncard - 1) ≥ Nat.factorial (Fintype.card V)) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (2 ^ (G.edgeSet.ncard - 1) ≥ Nat.factorial (Fintype.card V)) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (2 ^ (G.edgeSet.ncard - 1) ≥ Nat.factorial (Fintype.card V)) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (2 ^ (G.edgeSet.ncard - 1) ≥ Nat.factorial (Fintype.card V)) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (2 ^ (G.edgeSet.ncard - 1) ≥ Nat.factorial (Fintype.card V)) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (2 ^ (G.edgeSet.ncard - 1) ≥ Nat.factorial (Fintype.card V)) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (2 ^ (G.edgeSet.ncard - 1) ≥ Nat.factorial (Fintype.card V)) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : 3 ^ (G.edgeSet.ncard - 1) > Nat.factorial (Fintype.card V)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : 3 ^ (G.edgeSet.ncard - 1) > Nat.factorial (Fintype.card V)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : 3 ^ (G.edgeSet.ncard - 1) > Nat.factorial (Fintype.card V)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : 3 ^ (G.edgeSet.ncard - 1) > Nat.factorial (Fintype.card V)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : 3 ^ (G.edgeSet.ncard - 1) > Nat.factorial (Fintype.card V)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : 3 ^ (G.edgeSet.ncard - 1) > Nat.factorial (Fintype.card V)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : 3 ^ (G.edgeSet.ncard - 1) > Nat.factorial (Fintype.card V)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : 3 ^ (G.edgeSet.ncard - 1) > Nat.factorial (Fintype.card V)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : 3 ^ (G.edgeSet.ncard - 1) > Nat.factorial (Fintype.card V)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : 3 ^ (G.edgeSet.ncard - 1) > Nat.factorial (Fintype.card V)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : 3 ^ (G.edgeSet.ncard - 1) > Nat.factorial (Fintype.card V)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : 3 ^ (G.edgeSet.ncard - 1) > Nat.factorial (Fintype.card V)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : 3 ^ (G.edgeSet.ncard - 1) > Nat.factorial (Fintype.card V)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : 3 ^ (G.edgeSet.ncard - 1) > Nat.factorial (Fintype.card V)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : 3 ^ (G.edgeSet.ncard - 1) > Nat.factorial (Fintype.card V)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (3 ^ (G.edgeSet.ncard - 1) > Nat.factorial (Fintype.card V)) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (3 ^ (G.edgeSet.ncard - 1) > Nat.factorial (Fintype.card V)) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (3 ^ (G.edgeSet.ncard - 1) > Nat.factorial (Fintype.card V)) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (3 ^ (G.edgeSet.ncard - 1) > Nat.factorial (Fintype.card V)) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (3 ^ (G.edgeSet.ncard - 1) > Nat.factorial (Fintype.card V)) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (3 ^ (G.edgeSet.ncard - 1) > Nat.factorial (Fintype.card V)) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (3 ^ (G.edgeSet.ncard - 1) > Nat.factorial (Fintype.card V)) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) →
    (∀ {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H), Nonempty (G ≃g H)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (h : EdgeHypomorphic G H) :
    (Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1)) (h : EdgeHypomorphic G H) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
