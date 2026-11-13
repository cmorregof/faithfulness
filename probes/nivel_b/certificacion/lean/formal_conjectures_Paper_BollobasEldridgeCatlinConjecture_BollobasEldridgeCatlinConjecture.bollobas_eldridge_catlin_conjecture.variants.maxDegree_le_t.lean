import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# The Bollobás–Eldridge–Catlin conjecture on graph packing (1978)

*References:*
* [BE78] Bollobás, B. and Eldridge, S. E. (1978). "Packings of graphs and applications to
  computational complexity." *J. Combin. Theory Ser. B* 25, pp. 105--124.
* [Ca74] Catlin, P. A. (1974). "Subgraphs of graphs, I." *Discrete Math.* 10, pp. 225--233.
* [SS78] Sauer, N. and Spencer, J. (1978). "Edge disjoint placement of graphs."
  *J. Combin. Theory Ser. B* 25, pp. 295--302.
* [AF93] Aigner, M. and Brandt, S. (1993). "Embedding arbitrary graphs of maximum degree two."
  *J. London Math. Soc.* 48, pp. 39--51.
* [CSS03] Csaba, B., Shokoufandeh, A. and Szemerédi, E. (2003). "Proof of a conjecture of
  Bollobás and Eldridge for graphs of maximum degree three." *Combinatorica* 23, pp. 35--72.
-/

section

open SimpleGraph

namespace BollobasEldridgeCatlinConjecture

variable {V : Type*}

/-- Two graphs `G₁`, `G₂` on the same finite vertex set **pack** if some permutation of the
vertices makes their edge sets disjoint. -/
def Packs (G₁ G₂ : SimpleGraph V) : Prop :=
  ∃ σ : Equiv.Perm V, ∀ u v, G₁.Adj u v → ¬ G₂.Adj (σ u) (σ v)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    (G₁.maxDegree ≤ 2) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    (G₁.maxDegree ≤ 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    (G₁.maxDegree ≤ 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    (G₁.maxDegree ≤ 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    (G₁.maxDegree ≤ 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    (G₁.maxDegree ≤ 2) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    (G₁.maxDegree ≤ 2) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree < 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree < 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree < 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree < 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree < 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree < 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree < 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree < 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    (G₁.maxDegree ≤ 2) ↔ (G₁.maxDegree < 2) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    (G₁.maxDegree ≤ 2) ↔ (G₁.maxDegree < 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    (G₁.maxDegree ≤ 2) ↔ (G₁.maxDegree < 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    (G₁.maxDegree ≤ 2) ↔ (G₁.maxDegree < 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    (G₁.maxDegree ≤ 2) ↔ (G₁.maxDegree < 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    (G₁.maxDegree ≤ 2) ↔ (G₁.maxDegree < 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    (G₁.maxDegree ≤ 2) ↔ (G₁.maxDegree < 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 3) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 3) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 3) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 3) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 3) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 3) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 3) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 3) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    (G₁.maxDegree ≤ 2) ↔ (G₁.maxDegree ≤ 3) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    (G₁.maxDegree ≤ 2) ↔ (G₁.maxDegree ≤ 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    (G₁.maxDegree ≤ 2) ↔ (G₁.maxDegree ≤ 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    (G₁.maxDegree ≤ 2) ↔ (G₁.maxDegree ≤ 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    (G₁.maxDegree ≤ 2) ↔ (G₁.maxDegree ≤ 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    (G₁.maxDegree ≤ 2) ↔ (G₁.maxDegree ≤ 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    (G₁.maxDegree ≤ 2) ↔ (G₁.maxDegree ≤ 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : 2 ≥ G₁.maxDegree) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] :
    (G₁.maxDegree ≤ 2) ↔ (2 ≥ G₁.maxDegree) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] :
    (G₁.maxDegree ≤ 2) ↔ (2 ≥ G₁.maxDegree) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] :
    (G₁.maxDegree ≤ 2) ↔ (2 ≥ G₁.maxDegree) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] :
    (G₁.maxDegree ≤ 2) ↔ (2 ≥ G₁.maxDegree) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] :
    (G₁.maxDegree ≤ 2) ↔ (2 ≥ G₁.maxDegree) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] :
    (G₁.maxDegree ≤ 2) ↔ (2 ≥ G₁.maxDegree) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] :
    (G₁.maxDegree ≤ 2) ↔ (2 ≥ G₁.maxDegree) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] :
    (G₁.maxDegree ≤ 2) ↔ (2 ≥ G₁.maxDegree) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : 2 ≥ G₁.maxDegree) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : 2 ≥ G₁.maxDegree) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : 2 ≥ G₁.maxDegree) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : 2 ≥ G₁.maxDegree) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) (hΔ : G₁.maxDegree ≤ 2), Packs G₁ G₂

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) (hΔ : G₁.maxDegree ≤ 2), Packs G₁ G₂) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) (hΔ : G₁.maxDegree ≤ 2), Packs G₁ G₂) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) (hΔ : G₁.maxDegree ≤ 2), Packs G₁ G₂) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) (hΔ : G₁.maxDegree ≤ 2), Packs G₁ G₂) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ₀ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ₀ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ₀ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ₀ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ₀ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : 2 > G₁.maxDegree) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : 2 > G₁.maxDegree) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : 2 > G₁.maxDegree) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : 2 > G₁.maxDegree) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : 2 > G₁.maxDegree) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : 2 > G₁.maxDegree) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : 2 > G₁.maxDegree) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : 2 > G₁.maxDegree) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    (G₁.maxDegree ≤ 2) ↔ (2 > G₁.maxDegree) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    (G₁.maxDegree ≤ 2) ↔ (2 > G₁.maxDegree) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    (G₁.maxDegree ≤ 2) ↔ (2 > G₁.maxDegree) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    (G₁.maxDegree ≤ 2) ↔ (2 > G₁.maxDegree) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    (G₁.maxDegree ≤ 2) ↔ (2 > G₁.maxDegree) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    (G₁.maxDegree ≤ 2) ↔ (2 > G₁.maxDegree) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    (G₁.maxDegree ≤ 2) ↔ (2 > G₁.maxDegree) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : 3 ≥ G₁.maxDegree) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : 3 ≥ G₁.maxDegree) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : 3 ≥ G₁.maxDegree) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : 3 ≥ G₁.maxDegree) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : 3 ≥ G₁.maxDegree) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : 3 ≥ G₁.maxDegree) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : 3 ≥ G₁.maxDegree) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : 3 ≥ G₁.maxDegree) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    (G₁.maxDegree ≤ 2) ↔ (3 ≥ G₁.maxDegree) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    (G₁.maxDegree ≤ 2) ↔ (3 ≥ G₁.maxDegree) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    (G₁.maxDegree ≤ 2) ↔ (3 ≥ G₁.maxDegree) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    (G₁.maxDegree ≤ 2) ↔ (3 ≥ G₁.maxDegree) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    (G₁.maxDegree ≤ 2) ↔ (3 ≥ G₁.maxDegree) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    (G₁.maxDegree ≤ 2) ↔ (3 ≥ G₁.maxDegree) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    (G₁.maxDegree ≤ 2) ↔ (3 ≥ G₁.maxDegree) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1), Packs G₁ G₂) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    (G₁.maxDegree ≤ 2) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    (G₁.maxDegree ≤ 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    (G₁.maxDegree ≤ 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    (G₁.maxDegree ≤ 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    (G₁.maxDegree ≤ 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    (G₁.maxDegree ≤ 2) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    (G₁.maxDegree ≤ 2) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (hΔ : G₁.maxDegree ≤ 2) (h : (G₁.maxDegree + 1) * (G₂.maxDegree + 1) ≤ Fintype.card V + 1) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
