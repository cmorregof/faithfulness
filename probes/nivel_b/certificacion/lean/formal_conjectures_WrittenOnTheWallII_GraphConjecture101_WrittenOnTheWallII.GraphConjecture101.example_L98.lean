import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Written on the Wall II - Conjecture 101

*References:*
- [E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
- [LM11] V. E. Levit and E. Mandrescu, [A Set and Collection Lemma](https://arxiv.org/abs/1101.4564), 2011, Corollaries 2.3–2.4.
- [Li26] Wentao Li, [Lean proof of WOWII 101](https://github.com/VictorLiwentao/lean-graph-proofs/blob/9ce66be23570e0a9c8a6ae3f19f52e642878a8a9/proofs/WOWII101/PROOF.md), 2026.

## Definitions

The **$\alpha$-core** of a graph $G$, written `alphaCore G`, is the set of vertices
$v$ such that removing $v$ strictly decreases the independence number:
$$\mathrm{alphaCore}(G) = \{v \mid \alpha(G - v) < \alpha(G)\}$$
where $G - v$ is the subgraph of $G$ induced on $V(G) \setminus \{v\}$.

These vertices are also called "critical vertices for independence."
-/

section

namespace WrittenOnTheWallII.GraphConjecture101

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The independence number of the subgraph induced on $V \setminus \{v\}$
(i.e., the graph $G - v$). -/
noncomputable def indepNumDeleteVertex (G : SimpleGraph α) (v : α) : ℕ :=
  (G.induce (Set.univ \ {v})).indepNum

/-- The $\alpha$-core of $G$: the set of vertices whose removal strictly decreases the
independence number. A vertex $v$ is in the $\alpha$-core if $\alpha(G - v) < \alpha(G)$. -/
noncomputable def alphaCore (G : SimpleGraph α) : Finset α :=
  Finset.univ.filter (fun v => indepNumDeleteVertex G v < G.indepNum)

-- Sanity checks

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v ≤ G.indepNum

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v ≤ G.indepNum) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v ≤ G.indepNum) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v ≤ G.indepNum) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v ≤ G.indepNum) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v ≤ G.indepNum) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v ≤ G.indepNum) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v ≤ G.indepNum) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v > G.indepNum

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v > G.indepNum) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v > G.indepNum) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v > G.indepNum) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v > G.indepNum) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v > G.indepNum) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v > G.indepNum) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v > G.indepNum) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v > G.indepNum) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v > G.indepNum) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v > G.indepNum) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v > G.indepNum) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v > G.indepNum) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v > G.indepNum) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v > G.indepNum) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), G.indepNum > indepNumDeleteVertex G v

set_option maxHeartbeats 200000 in
example (G : SimpleGraph (Fin 3)) (v : Fin 3) :
    (indepNumDeleteVertex G v < G.indepNum) ↔ (G.indepNum > indepNumDeleteVertex G v) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (G : SimpleGraph (Fin 3)) (v : Fin 3) :
    (indepNumDeleteVertex G v < G.indepNum) ↔ (G.indepNum > indepNumDeleteVertex G v) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph (Fin 3)) (v : Fin 3) :
    (indepNumDeleteVertex G v < G.indepNum) ↔ (G.indepNum > indepNumDeleteVertex G v) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph (Fin 3)) (v : Fin 3) :
    (indepNumDeleteVertex G v < G.indepNum) ↔ (G.indepNum > indepNumDeleteVertex G v) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph (Fin 3)) (v : Fin 3) :
    (indepNumDeleteVertex G v < G.indepNum) ↔ (G.indepNum > indepNumDeleteVertex G v) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (G : SimpleGraph (Fin 3)) (v : Fin 3) :
    (indepNumDeleteVertex G v < G.indepNum) ↔ (G.indepNum > indepNumDeleteVertex G v) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph (Fin 3)) (v : Fin 3) :
    (indepNumDeleteVertex G v < G.indepNum) ↔ (G.indepNum > indepNumDeleteVertex G v) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph (Fin 3)) (v : Fin 3) :
    (indepNumDeleteVertex G v < G.indepNum) ↔ (G.indepNum > indepNumDeleteVertex G v) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) ↔
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), G.indepNum > indepNumDeleteVertex G v) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) ↔
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), G.indepNum > indepNumDeleteVertex G v) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) ↔
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), G.indepNum > indepNumDeleteVertex G v) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) ↔
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), G.indepNum > indepNumDeleteVertex G v) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv₀ : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) ↔
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv₀ : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) ↔
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv₀ : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) ↔
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv₀ : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) ↔
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv₀ : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), G.indepNum ≥ indepNumDeleteVertex G v

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), G.indepNum ≥ indepNumDeleteVertex G v) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), G.indepNum ≥ indepNumDeleteVertex G v) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), G.indepNum ≥ indepNumDeleteVertex G v) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), G.indepNum ≥ indepNumDeleteVertex G v) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), G.indepNum ≥ indepNumDeleteVertex G v) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), G.indepNum ≥ indepNumDeleteVertex G v) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), G.indepNum ≥ indepNumDeleteVertex G v) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), G.indepNum < indepNumDeleteVertex G v

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), G.indepNum < indepNumDeleteVertex G v) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), G.indepNum < indepNumDeleteVertex G v) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), G.indepNum < indepNumDeleteVertex G v) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), G.indepNum < indepNumDeleteVertex G v) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), G.indepNum < indepNumDeleteVertex G v) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), G.indepNum < indepNumDeleteVertex G v) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), G.indepNum < indepNumDeleteVertex G v) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), G.indepNum < indepNumDeleteVertex G v) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), G.indepNum < indepNumDeleteVertex G v) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), G.indepNum < indepNumDeleteVertex G v) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), G.indepNum < indepNumDeleteVertex G v) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), G.indepNum < indepNumDeleteVertex G v) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), G.indepNum < indepNumDeleteVertex G v) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), indepNumDeleteVertex G v < G.indepNum) →
    (∀ (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G), G.indepNum < indepNumDeleteVertex G v) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (G : SimpleGraph (Fin 3)) (v : Fin 3) (hv : v ∈ alphaCore G) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
