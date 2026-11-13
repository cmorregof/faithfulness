import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 619

*References:*
- [erdosproblems.com/619](https://www.erdosproblems.com/619)
- [EGR98] Erdős, Paul and Gyárfás, András and Ruszinkó, Miklós, *How to decrease the
  diameter of triangle-free graphs*. Combinatorica **18** (1998), 493-501.
- [Er99] Erdős, Paul, *A selection of problems and results in combinatorics*.
  Combin. Probab. Comput. **8** (1999), 1-6.
-/

section

open SimpleGraph

namespace Erdos619

/--
For a graph $G$, `minNewEdges r G` is the smallest number of edges that need to be added
to $G$ so that it has diameter at most $r$, while preserving the property of being
triangle-free. Erdős, Gyárfás and Ruszinkó denote this quantity by $h_r(G)$ in [EGR98].

Adding edges is formalised as passing to a supergraph `H ≥ G` on the same vertex set, the
number of added edges being the (finite) cardinality of the edge set of `H \ G`. We use
the extended diameter `SimpleGraph.ediam` (valued in `ℕ∞`) so that disconnected
supergraphs, which have infinite diameter, do not qualify. If no triangle-free supergraph
of `G` of diameter at most `r` exists, then `minNewEdges r G = 0` by the `Nat.sInf`
convention on the empty set; `erdos_619.variants.add_edges_diam_three` shows this
degenerate case does not occur for connected triangle-free `G` when `3 ≤ r`.
-/
noncomputable def minNewEdges {V : Type*} (r : ℕ) (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ H : SimpleGraph V,
    G ≤ H ∧ H.CliqueFree 3 ∧ H.ediam ≤ r ∧ (H \ G).edgeSet.ncard = k}

/-
## Partial results
-/

/-
## Sanity checks
-/

universe u_c1 u_c2 u_c3 u_c4 u_c5 u_c6 u_c7 u_c8 u_c9 u_c10 u_c11 u_c12 u_c13 u_c14 u_c15 u_c16 u_c17 u_c18 u_c19 u_c20 u_c21 u_c22
set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c1} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c2} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3), minNewEdges r G = 0

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c2} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3), minNewEdges r G = 0) →
    (∀ {V : Type u_c1} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c2} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3), minNewEdges r G = 0) →
    (∀ {V : Type u_c1} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c2} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3), minNewEdges r G = 0) →
    (∀ {V : Type u_c1} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c2} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3), minNewEdges r G = 0) →
    (∀ {V : Type u_c1} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c2} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3), minNewEdges r G = 0) →
    (∀ {V : Type u_c1} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c2} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3), minNewEdges r G = 0) →
    (∀ {V : Type u_c1} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c2} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3), minNewEdges r G = 0) →
    (∀ {V : Type u_c1} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type u_c3} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) :
    (G.ediam ≤ r) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type u_c3} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) :
    (G.ediam ≤ r) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type u_c3} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) :
    (G.ediam ≤ r) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type u_c3} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) :
    (G.ediam ≤ r) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type u_c3} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) :
    (G.ediam ≤ r) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type u_c3} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) :
    (G.ediam ≤ r) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type u_c3} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) :
    (G.ediam ≤ r) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c4} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c5} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam < r), minNewEdges r G = 0

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c4} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0) →
    (∀ {V : Type u_c5} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam < r), minNewEdges r G = 0) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c4} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0) →
    (∀ {V : Type u_c5} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam < r), minNewEdges r G = 0) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c4} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0) →
    (∀ {V : Type u_c5} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam < r), minNewEdges r G = 0) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c4} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0) →
    (∀ {V : Type u_c5} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam < r), minNewEdges r G = 0) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c4} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0) →
    (∀ {V : Type u_c5} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam < r), minNewEdges r G = 0) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c4} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0) →
    (∀ {V : Type u_c5} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam < r), minNewEdges r G = 0) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c4} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0) →
    (∀ {V : Type u_c5} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam < r), minNewEdges r G = 0) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type u_c6} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) :
    (G.ediam ≤ r) ↔ (G.ediam < r) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type u_c6} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) :
    (G.ediam ≤ r) ↔ (G.ediam < r) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type u_c6} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) :
    (G.ediam ≤ r) ↔ (G.ediam < r) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type u_c6} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) :
    (G.ediam ≤ r) ↔ (G.ediam < r) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type u_c6} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) :
    (G.ediam ≤ r) ↔ (G.ediam < r) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type u_c6} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) :
    (G.ediam ≤ r) ↔ (G.ediam < r) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type u_c6} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) :
    (G.ediam ≤ r) ↔ (G.ediam < r) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c7} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c8} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : r ≥ G.ediam), minNewEdges r G = 0

set_option maxHeartbeats 200000 in
example {V : Type u_c9} {r : ℕ} {G : SimpleGraph V} :
    (G.ediam ≤ r) ↔ (r ≥ G.ediam) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {V : Type u_c9} {r : ℕ} {G : SimpleGraph V} :
    (G.ediam ≤ r) ↔ (r ≥ G.ediam) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {V : Type u_c9} {r : ℕ} {G : SimpleGraph V} :
    (G.ediam ≤ r) ↔ (r ≥ G.ediam) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {V : Type u_c9} {r : ℕ} {G : SimpleGraph V} :
    (G.ediam ≤ r) ↔ (r ≥ G.ediam) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {V : Type u_c9} {r : ℕ} {G : SimpleGraph V} :
    (G.ediam ≤ r) ↔ (r ≥ G.ediam) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {V : Type u_c9} {r : ℕ} {G : SimpleGraph V} :
    (G.ediam ≤ r) ↔ (r ≥ G.ediam) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type u_c9} {r : ℕ} {G : SimpleGraph V} :
    (G.ediam ≤ r) ↔ (r ≥ G.ediam) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {V : Type u_c9} {r : ℕ} {G : SimpleGraph V} :
    (G.ediam ≤ r) ↔ (r ≥ G.ediam) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c7} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0) ↔
    (∀ {V : Type u_c8} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : r ≥ G.ediam), minNewEdges r G = 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c7} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0) ↔
    (∀ {V : Type u_c8} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : r ≥ G.ediam), minNewEdges r G = 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c7} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0) ↔
    (∀ {V : Type u_c8} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : r ≥ G.ediam), minNewEdges r G = 0) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c7} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0) ↔
    (∀ {V : Type u_c8} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : r ≥ G.ediam), minNewEdges r G = 0) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c10} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c11} {r : ℕ} {G : SimpleGraph V} (hdiam : G.ediam ≤ r) (hG : G.CliqueFree 3), minNewEdges r G = 0

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c10} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0) ↔
    (∀ {V : Type u_c11} {r : ℕ} {G : SimpleGraph V} (hdiam : G.ediam ≤ r) (hG : G.CliqueFree 3), minNewEdges r G = 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c10} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0) ↔
    (∀ {V : Type u_c11} {r : ℕ} {G : SimpleGraph V} (hdiam : G.ediam ≤ r) (hG : G.CliqueFree 3), minNewEdges r G = 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c10} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0) ↔
    (∀ {V : Type u_c11} {r : ℕ} {G : SimpleGraph V} (hdiam : G.ediam ≤ r) (hG : G.CliqueFree 3), minNewEdges r G = 0) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c10} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0) ↔
    (∀ {V : Type u_c11} {r : ℕ} {G : SimpleGraph V} (hdiam : G.ediam ≤ r) (hG : G.CliqueFree 3), minNewEdges r G = 0) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c13} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c14} {r : ℕ} {G : SimpleGraph V} (hG₀ : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c13} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0) ↔
    (∀ {V : Type u_c14} {r : ℕ} {G : SimpleGraph V} (hG₀ : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c13} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0) ↔
    (∀ {V : Type u_c14} {r : ℕ} {G : SimpleGraph V} (hG₀ : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c13} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0) ↔
    (∀ {V : Type u_c14} {r : ℕ} {G : SimpleGraph V} (hG₀ : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c13} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0) ↔
    (∀ {V : Type u_c14} {r : ℕ} {G : SimpleGraph V} (hG₀ : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c16} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c17} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : r > G.ediam), minNewEdges r G = 0

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c16} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0) →
    (∀ {V : Type u_c17} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : r > G.ediam), minNewEdges r G = 0) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c16} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0) →
    (∀ {V : Type u_c17} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : r > G.ediam), minNewEdges r G = 0) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c16} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0) →
    (∀ {V : Type u_c17} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : r > G.ediam), minNewEdges r G = 0) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c16} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0) →
    (∀ {V : Type u_c17} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : r > G.ediam), minNewEdges r G = 0) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c16} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0) →
    (∀ {V : Type u_c17} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : r > G.ediam), minNewEdges r G = 0) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c16} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0) →
    (∀ {V : Type u_c17} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : r > G.ediam), minNewEdges r G = 0) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c16} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0) →
    (∀ {V : Type u_c17} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : r > G.ediam), minNewEdges r G = 0) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type u_c18} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) :
    (G.ediam ≤ r) ↔ (r > G.ediam) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type u_c18} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) :
    (G.ediam ≤ r) ↔ (r > G.ediam) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type u_c18} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) :
    (G.ediam ≤ r) ↔ (r > G.ediam) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type u_c18} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) :
    (G.ediam ≤ r) ↔ (r > G.ediam) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type u_c18} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) :
    (G.ediam ≤ r) ↔ (r > G.ediam) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type u_c18} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) :
    (G.ediam ≤ r) ↔ (r > G.ediam) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type u_c18} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) :
    (G.ediam ≤ r) ↔ (r > G.ediam) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c19} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c20} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3), minNewEdges r G = 0

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c20} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3), minNewEdges r G = 0) →
    (∀ {V : Type u_c19} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c20} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3), minNewEdges r G = 0) →
    (∀ {V : Type u_c19} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c20} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3), minNewEdges r G = 0) →
    (∀ {V : Type u_c19} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c20} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3), minNewEdges r G = 0) →
    (∀ {V : Type u_c19} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c20} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3), minNewEdges r G = 0) →
    (∀ {V : Type u_c19} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c20} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3), minNewEdges r G = 0) →
    (∀ {V : Type u_c19} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c20} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3), minNewEdges r G = 0) →
    (∀ {V : Type u_c19} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r), minNewEdges r G = 0) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type u_c21} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) :
    (G.ediam ≤ r) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type u_c21} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) :
    (G.ediam ≤ r) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type u_c21} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) :
    (G.ediam ≤ r) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type u_c21} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) :
    (G.ediam ≤ r) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type u_c21} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) :
    (G.ediam ≤ r) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type u_c21} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) :
    (G.ediam ≤ r) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type u_c21} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) :
    (G.ediam ≤ r) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example {V : Type u_c22} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {V : Type u_c22} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type u_c22} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {V : Type u_c22} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type u_c22} {r : ℕ} {G : SimpleGraph V} (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
