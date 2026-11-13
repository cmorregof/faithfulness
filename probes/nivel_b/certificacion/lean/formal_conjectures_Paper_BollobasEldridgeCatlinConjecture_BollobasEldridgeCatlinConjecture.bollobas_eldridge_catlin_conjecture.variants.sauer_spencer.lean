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
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj], Packs G₁ G₂

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj], Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj], Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj], Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj], Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj], Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj], Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj], Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]  :
    (2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]  :
    (2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]  :
    (2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]  :
    (2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]  :
    (2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]  :
    (2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]  :
    (2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree ≤ Fintype.card V), Packs G₁ G₂

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree ≤ Fintype.card V), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree ≤ Fintype.card V), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree ≤ Fintype.card V), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree ≤ Fintype.card V), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree ≤ Fintype.card V), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree ≤ Fintype.card V), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree ≤ Fintype.card V), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]  :
    (2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) ↔ (2 * G₁.maxDegree * G₂.maxDegree ≤ Fintype.card V) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]  :
    (2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) ↔ (2 * G₁.maxDegree * G₂.maxDegree ≤ Fintype.card V) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]  :
    (2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) ↔ (2 * G₁.maxDegree * G₂.maxDegree ≤ Fintype.card V) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]  :
    (2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) ↔ (2 * G₁.maxDegree * G₂.maxDegree ≤ Fintype.card V) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]  :
    (2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) ↔ (2 * G₁.maxDegree * G₂.maxDegree ≤ Fintype.card V) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]  :
    (2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) ↔ (2 * G₁.maxDegree * G₂.maxDegree ≤ Fintype.card V) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]  :
    (2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) ↔ (2 * G₁.maxDegree * G₂.maxDegree ≤ Fintype.card V) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 3 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 3 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 3 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 3 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 3 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 3 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 3 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 3 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 3 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 3 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 3 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 3 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 3 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 3 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 3 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]  :
    (2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) ↔ (3 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]  :
    (2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) ↔ (3 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]  :
    (2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) ↔ (3 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]  :
    (2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) ↔ (3 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]  :
    (2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) ↔ (3 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]  :
    (2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) ↔ (3 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]  :
    (2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) ↔ (3 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : Fintype.card V > 2 * G₁.maxDegree * G₂.maxDegree), Packs G₁ G₂

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] :
    (2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) ↔ (Fintype.card V > 2 * G₁.maxDegree * G₂.maxDegree) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] :
    (2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) ↔ (Fintype.card V > 2 * G₁.maxDegree * G₂.maxDegree) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] :
    (2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) ↔ (Fintype.card V > 2 * G₁.maxDegree * G₂.maxDegree) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] :
    (2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) ↔ (Fintype.card V > 2 * G₁.maxDegree * G₂.maxDegree) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] :
    (2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) ↔ (Fintype.card V > 2 * G₁.maxDegree * G₂.maxDegree) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] :
    (2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) ↔ (Fintype.card V > 2 * G₁.maxDegree * G₂.maxDegree) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] :
    (2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) ↔ (Fintype.card V > 2 * G₁.maxDegree * G₂.maxDegree) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] :
    (2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) ↔ (Fintype.card V > 2 * G₁.maxDegree * G₂.maxDegree) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : Fintype.card V > 2 * G₁.maxDegree * G₂.maxDegree), Packs G₁ G₂) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : Fintype.card V > 2 * G₁.maxDegree * G₂.maxDegree), Packs G₁ G₂) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : Fintype.card V > 2 * G₁.maxDegree * G₂.maxDegree), Packs G₁ G₂) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : Fintype.card V > 2 * G₁.maxDegree * G₂.maxDegree), Packs G₁ G₂) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h₀ : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h₀ : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h₀ : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h₀ : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h₀ : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : Fintype.card V ≥ 2 * G₁.maxDegree * G₂.maxDegree), Packs G₁ G₂

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : Fintype.card V ≥ 2 * G₁.maxDegree * G₂.maxDegree), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : Fintype.card V ≥ 2 * G₁.maxDegree * G₂.maxDegree), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : Fintype.card V ≥ 2 * G₁.maxDegree * G₂.maxDegree), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : Fintype.card V ≥ 2 * G₁.maxDegree * G₂.maxDegree), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : Fintype.card V ≥ 2 * G₁.maxDegree * G₂.maxDegree), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : Fintype.card V ≥ 2 * G₁.maxDegree * G₂.maxDegree), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : Fintype.card V ≥ 2 * G₁.maxDegree * G₂.maxDegree), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]  :
    (2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) ↔ (Fintype.card V ≥ 2 * G₁.maxDegree * G₂.maxDegree) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]  :
    (2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) ↔ (Fintype.card V ≥ 2 * G₁.maxDegree * G₂.maxDegree) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]  :
    (2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) ↔ (Fintype.card V ≥ 2 * G₁.maxDegree * G₂.maxDegree) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]  :
    (2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) ↔ (Fintype.card V ≥ 2 * G₁.maxDegree * G₂.maxDegree) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]  :
    (2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) ↔ (Fintype.card V ≥ 2 * G₁.maxDegree * G₂.maxDegree) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]  :
    (2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) ↔ (Fintype.card V ≥ 2 * G₁.maxDegree * G₂.maxDegree) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]  :
    (2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) ↔ (Fintype.card V ≥ 2 * G₁.maxDegree * G₂.maxDegree) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : Fintype.card V > 3 * G₁.maxDegree * G₂.maxDegree), Packs G₁ G₂

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : Fintype.card V > 3 * G₁.maxDegree * G₂.maxDegree), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : Fintype.card V > 3 * G₁.maxDegree * G₂.maxDegree), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : Fintype.card V > 3 * G₁.maxDegree * G₂.maxDegree), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : Fintype.card V > 3 * G₁.maxDegree * G₂.maxDegree), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : Fintype.card V > 3 * G₁.maxDegree * G₂.maxDegree), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : Fintype.card V > 3 * G₁.maxDegree * G₂.maxDegree), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : Fintype.card V > 3 * G₁.maxDegree * G₂.maxDegree), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : Fintype.card V > 3 * G₁.maxDegree * G₂.maxDegree), Packs G₁ G₂) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : Fintype.card V > 3 * G₁.maxDegree * G₂.maxDegree), Packs G₁ G₂) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : Fintype.card V > 3 * G₁.maxDegree * G₂.maxDegree), Packs G₁ G₂) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : Fintype.card V > 3 * G₁.maxDegree * G₂.maxDegree), Packs G₁ G₂) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : Fintype.card V > 3 * G₁.maxDegree * G₂.maxDegree), Packs G₁ G₂) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : Fintype.card V > 3 * G₁.maxDegree * G₂.maxDegree), Packs G₁ G₂) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V), Packs G₁ G₂) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : Fintype.card V > 3 * G₁.maxDegree * G₂.maxDegree), Packs G₁ G₂) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]  :
    (2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) ↔ (Fintype.card V > 3 * G₁.maxDegree * G₂.maxDegree) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]  :
    (2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) ↔ (Fintype.card V > 3 * G₁.maxDegree * G₂.maxDegree) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]  :
    (2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) ↔ (Fintype.card V > 3 * G₁.maxDegree * G₂.maxDegree) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]  :
    (2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) ↔ (Fintype.card V > 3 * G₁.maxDegree * G₂.maxDegree) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]  :
    (2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) ↔ (Fintype.card V > 3 * G₁.maxDegree * G₂.maxDegree) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]  :
    (2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) ↔ (Fintype.card V > 3 * G₁.maxDegree * G₂.maxDegree) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]  :
    (2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) ↔ (Fintype.card V > 3 * G₁.maxDegree * G₂.maxDegree) := by
  plausible

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : 2 * G₁.maxDegree * G₂.maxDegree < Fintype.card V) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
