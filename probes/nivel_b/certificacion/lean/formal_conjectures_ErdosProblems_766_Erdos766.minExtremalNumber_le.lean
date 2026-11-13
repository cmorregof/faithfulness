import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 766

*References:*
- [erdosproblems.com/766](https://www.erdosproblems.com/766)
- [Er64c] Erdős, P., *Extremal problems in graph theory*. Theory of Graphs and its Applications
  (Proc. Sympos. Smolenice, 1963) (1964), 29-36.
  [PDF](https://www.renyi.hu/~p_erdos/1964-06.pdf)
-/

section

open Filter
open scoped SimpleGraph

namespace Erdos766

/-- $f(n;k,l)$ in the sense of [Er64c], where it is called $f_1(n;k,l)$: the least $m$ such that
every graph with $n$ vertices and $m$ edges contains at least one graph with $k$ vertices and
$l$ edges as a (not necessarily induced) subgraph. There is no graph with $n$ vertices and more
than $\binom{n}{2}$ edges, so the set is nonempty. -/
noncomputable def forcingNumber (n k l : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G}

/-- The function of erdosproblems.com: the minimum of $\mathrm{ex}(n;G)$ over all graphs $G$ with
$k$ vertices and $l$ edges. In [Er64c] the least $m$ such that every graph with $n$ vertices and
$m$ edges contains one fixed graph with $k$ vertices and $l$ edges is called $f_2(n;k,l)$, so
this is $f_2(n;k,l) - 1$. The value is in `ℕ∞` and is `⊤` when no such graph $G$ exists. -/
noncomputable def minExtremalNumber (n k l : ℕ) : ℕ∞ :=
  ⨅ (G : SimpleGraph (Fin k)) (_ : G.edgeSet.ncard = l), (SimpleGraph.extremalNumber n G : ℕ∞)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l < SimpleGraph.extremalNumber n G

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l < SimpleGraph.extremalNumber n G) →
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l < SimpleGraph.extremalNumber n G) →
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l < SimpleGraph.extremalNumber n G) →
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l < SimpleGraph.extremalNumber n G) →
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l < SimpleGraph.extremalNumber n G) →
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l < SimpleGraph.extremalNumber n G) →
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l < SimpleGraph.extremalNumber n G) →
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≥ SimpleGraph.extremalNumber n G

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≥ SimpleGraph.extremalNumber n G) →
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≥ SimpleGraph.extremalNumber n G) →
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≥ SimpleGraph.extremalNumber n G) →
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≥ SimpleGraph.extremalNumber n G) →
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≥ SimpleGraph.extremalNumber n G) →
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≥ SimpleGraph.extremalNumber n G) →
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≥ SimpleGraph.extremalNumber n G) →
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) →
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≥ SimpleGraph.extremalNumber n G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) →
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≥ SimpleGraph.extremalNumber n G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) →
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≥ SimpleGraph.extremalNumber n G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) →
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≥ SimpleGraph.extremalNumber n G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) →
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≥ SimpleGraph.extremalNumber n G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) →
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≥ SimpleGraph.extremalNumber n G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) →
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≥ SimpleGraph.extremalNumber n G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), SimpleGraph.extremalNumber n G ≥ minExtremalNumber n k l

set_option maxHeartbeats 200000 in
example (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) :
    (minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) ↔ (SimpleGraph.extremalNumber n G ≥ minExtremalNumber n k l) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) :
    (minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) ↔ (SimpleGraph.extremalNumber n G ≥ minExtremalNumber n k l) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) :
    (minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) ↔ (SimpleGraph.extremalNumber n G ≥ minExtremalNumber n k l) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) :
    (minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) ↔ (SimpleGraph.extremalNumber n G ≥ minExtremalNumber n k l) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) :
    (minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) ↔ (SimpleGraph.extremalNumber n G ≥ minExtremalNumber n k l) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) :
    (minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) ↔ (SimpleGraph.extremalNumber n G ≥ minExtremalNumber n k l) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) :
    (minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) ↔ (SimpleGraph.extremalNumber n G ≥ minExtremalNumber n k l) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) :
    (minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) ↔ (SimpleGraph.extremalNumber n G ≥ minExtremalNumber n k l) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) ↔
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), SimpleGraph.extremalNumber n G ≥ minExtremalNumber n k l) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) ↔
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), SimpleGraph.extremalNumber n G ≥ minExtremalNumber n k l) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) ↔
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), SimpleGraph.extremalNumber n G ≥ minExtremalNumber n k l) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) ↔
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), SimpleGraph.extremalNumber n G ≥ minExtremalNumber n k l) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h₀ : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) ↔
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h₀ : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) ↔
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h₀ : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) ↔
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h₀ : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) ↔
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h₀ : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), SimpleGraph.extremalNumber n G > minExtremalNumber n k l

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), SimpleGraph.extremalNumber n G > minExtremalNumber n k l) →
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), SimpleGraph.extremalNumber n G > minExtremalNumber n k l) →
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), SimpleGraph.extremalNumber n G > minExtremalNumber n k l) →
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), SimpleGraph.extremalNumber n G > minExtremalNumber n k l) →
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), SimpleGraph.extremalNumber n G > minExtremalNumber n k l) →
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), SimpleGraph.extremalNumber n G > minExtremalNumber n k l) →
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), SimpleGraph.extremalNumber n G > minExtremalNumber n k l) →
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), SimpleGraph.extremalNumber n G ≤ minExtremalNumber n k l

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), SimpleGraph.extremalNumber n G ≤ minExtremalNumber n k l) →
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), SimpleGraph.extremalNumber n G ≤ minExtremalNumber n k l) →
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), SimpleGraph.extremalNumber n G ≤ minExtremalNumber n k l) →
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), SimpleGraph.extremalNumber n G ≤ minExtremalNumber n k l) →
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), SimpleGraph.extremalNumber n G ≤ minExtremalNumber n k l) →
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), SimpleGraph.extremalNumber n G ≤ minExtremalNumber n k l) →
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), SimpleGraph.extremalNumber n G ≤ minExtremalNumber n k l) →
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) →
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), SimpleGraph.extremalNumber n G ≤ minExtremalNumber n k l) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) →
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), SimpleGraph.extremalNumber n G ≤ minExtremalNumber n k l) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) →
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), SimpleGraph.extremalNumber n G ≤ minExtremalNumber n k l) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) →
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), SimpleGraph.extremalNumber n G ≤ minExtremalNumber n k l) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) →
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), SimpleGraph.extremalNumber n G ≤ minExtremalNumber n k l) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) →
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), SimpleGraph.extremalNumber n G ≤ minExtremalNumber n k l) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), minExtremalNumber n k l ≤ SimpleGraph.extremalNumber n G) →
    (∀ (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l), SimpleGraph.extremalNumber n G ≤ minExtremalNumber n k l) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) {k l : ℕ} (G : SimpleGraph (Fin k)) (h : G.edgeSet.ncard = l) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
