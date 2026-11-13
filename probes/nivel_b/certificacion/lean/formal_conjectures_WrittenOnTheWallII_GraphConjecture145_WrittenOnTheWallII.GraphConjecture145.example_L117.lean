import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Independence
/-!
# Written on the Wall II - Conjecture 145

The WOWII HTML uses $\lambda_{\min}(\overline{G})$ (the bar denotes graph complement).
The formal statement below uses the local-independence minimum of $G^c$.

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Definitions

The **local independence minimum** $\mathrm{lMin}(G)$ is:
$$\mathrm{lMin}(G) = \min_{v \in V(G)} l(v)$$
where $l(v) = \mathrm{indepNeighborsCard}(G, v)$ is the independence number of the
neighbourhood of $v$. This is the minimum over all vertices of the local
independence number.

The **boundary vertices** $B(G)$ of a connected graph are the vertices $v$ such
that the eccentricity of $v$ equals the diameter of $G$.

The **eccentricity of a set** $\mathrm{ecc}(S) = \max_{u \notin S} \min_{w \in S}
\mathrm{dist}(u, w)$. In the conjecture below, $\mathrm{ecc}(B)$ is the
eccentricity of the boundary set.

**Conjecture 145:** $\mathrm{tree}(G) \ge 2 \cdot \mathrm{ecc}(B) /
\lambda_{\min}(\overline{G})$ where $\mathrm{tree}(G)$ is `largestInducedTreeSize G`,
$\mathrm{ecc}(B)$ is the eccentricity of the boundary vertices, and
$\lambda_{\min}(\overline{G})$ is the local independence minimum of the complement
$\overline{G}$.
-/

section

namespace WrittenOnTheWallII.GraphConjecture145

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- `localIndependenceMin G` is the minimum over all vertices of the local independence
number `indepNeighborsCard G v`. This equals $\mathrm{lMin}$ from DeLaVina's notation. -/
noncomputable def localIndependenceMin (G : SimpleGraph α) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (indepNeighborsCard G)

-- Sanity checks

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G < indepNeighborsCard G v

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G < indepNeighborsCard G v) →
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G < indepNeighborsCard G v) →
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G < indepNeighborsCard G v) →
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G < indepNeighborsCard G v) →
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G < indepNeighborsCard G v) →
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G < indepNeighborsCard G v) →
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G < indepNeighborsCard G v) →
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≥ indepNeighborsCard G v

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≥ indepNeighborsCard G v) →
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≥ indepNeighborsCard G v) →
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≥ indepNeighborsCard G v) →
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≥ indepNeighborsCard G v) →
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≥ indepNeighborsCard G v) →
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≥ indepNeighborsCard G v) →
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≥ indepNeighborsCard G v) →
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v) →
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≥ indepNeighborsCard G v) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v) →
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≥ indepNeighborsCard G v) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v) →
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≥ indepNeighborsCard G v) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v) →
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≥ indepNeighborsCard G v) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v) →
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≥ indepNeighborsCard G v) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v) →
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≥ indepNeighborsCard G v) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v) →
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≥ indepNeighborsCard G v) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), indepNeighborsCard G v ≥ localIndependenceMin G

set_option maxHeartbeats 200000 in
example (G : SimpleGraph (Fin 4)) (v : Fin 4) :
    (localIndependenceMin G ≤ indepNeighborsCard G v) ↔ (indepNeighborsCard G v ≥ localIndependenceMin G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (G : SimpleGraph (Fin 4)) (v : Fin 4) :
    (localIndependenceMin G ≤ indepNeighborsCard G v) ↔ (indepNeighborsCard G v ≥ localIndependenceMin G) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph (Fin 4)) (v : Fin 4) :
    (localIndependenceMin G ≤ indepNeighborsCard G v) ↔ (indepNeighborsCard G v ≥ localIndependenceMin G) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph (Fin 4)) (v : Fin 4) :
    (localIndependenceMin G ≤ indepNeighborsCard G v) ↔ (indepNeighborsCard G v ≥ localIndependenceMin G) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph (Fin 4)) (v : Fin 4) :
    (localIndependenceMin G ≤ indepNeighborsCard G v) ↔ (indepNeighborsCard G v ≥ localIndependenceMin G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (G : SimpleGraph (Fin 4)) (v : Fin 4) :
    (localIndependenceMin G ≤ indepNeighborsCard G v) ↔ (indepNeighborsCard G v ≥ localIndependenceMin G) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph (Fin 4)) (v : Fin 4) :
    (localIndependenceMin G ≤ indepNeighborsCard G v) ↔ (indepNeighborsCard G v ≥ localIndependenceMin G) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph (Fin 4)) (v : Fin 4) :
    (localIndependenceMin G ≤ indepNeighborsCard G v) ↔ (indepNeighborsCard G v ≥ localIndependenceMin G) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v) ↔
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), indepNeighborsCard G v ≥ localIndependenceMin G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v) ↔
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), indepNeighborsCard G v ≥ localIndependenceMin G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v) ↔
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), indepNeighborsCard G v ≥ localIndependenceMin G) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v) ↔
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), indepNeighborsCard G v ≥ localIndependenceMin G) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), indepNeighborsCard G v > localIndependenceMin G

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), indepNeighborsCard G v > localIndependenceMin G) →
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), indepNeighborsCard G v > localIndependenceMin G) →
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), indepNeighborsCard G v > localIndependenceMin G) →
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), indepNeighborsCard G v > localIndependenceMin G) →
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), indepNeighborsCard G v > localIndependenceMin G) →
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), indepNeighborsCard G v > localIndependenceMin G) →
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), indepNeighborsCard G v > localIndependenceMin G) →
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), indepNeighborsCard G v ≤ localIndependenceMin G

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), indepNeighborsCard G v ≤ localIndependenceMin G) →
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), indepNeighborsCard G v ≤ localIndependenceMin G) →
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), indepNeighborsCard G v ≤ localIndependenceMin G) →
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), indepNeighborsCard G v ≤ localIndependenceMin G) →
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), indepNeighborsCard G v ≤ localIndependenceMin G) →
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), indepNeighborsCard G v ≤ localIndependenceMin G) →
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), indepNeighborsCard G v ≤ localIndependenceMin G) →
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v) →
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), indepNeighborsCard G v ≤ localIndependenceMin G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v) →
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), indepNeighborsCard G v ≤ localIndependenceMin G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v) →
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), indepNeighborsCard G v ≤ localIndependenceMin G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v) →
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), indepNeighborsCard G v ≤ localIndependenceMin G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v) →
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), indepNeighborsCard G v ≤ localIndependenceMin G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v) →
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), indepNeighborsCard G v ≤ localIndependenceMin G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), localIndependenceMin G ≤ indepNeighborsCard G v) →
    (∀ (G : SimpleGraph (Fin 4)) (v : Fin 4), indepNeighborsCard G v ≤ localIndependenceMin G) := by
  intro h; intros; aesop

#eval "FIN_CERTIFICAR"
