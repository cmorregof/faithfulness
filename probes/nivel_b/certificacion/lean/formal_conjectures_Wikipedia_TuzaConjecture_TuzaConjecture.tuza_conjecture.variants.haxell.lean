import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Tuza's conjecture

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Tuza%27s_conjecture)
* [Tu90] Tuza, Zs. (1990). "A conjecture on triangles of graphs." *Graphs Combin.* 6,
  pp. 373--380.
* [Ha99] Haxell, P. E. (1999). "Packing and covering triangles in graphs." *Discrete Math.*
  195, pp. 251--254.
-/

section

namespace TuzaConjecture

variable {V : Type*}

/-- `C` is a **triangle cover** of `G`: a set of edges of `G` meeting every triangle of `G`.
Removing the edges of `C` from `G` leaves a triangle-free graph. -/
def IsTriangleCover (G : SimpleGraph V) (C : Set (Sym2 V)) : Prop :=
  C ⊆ G.edgeSet ∧ ∀ t : Finset V, G.IsNClique 3 t → ∃ e ∈ C, ∀ x ∈ e, x ∈ t

/-- `T` is a **triangle packing** of `G`: a set of pairwise edge-disjoint triangles of `G`.
Two distinct triangles are edge-disjoint exactly when they share at most one vertex. -/
def IsTrianglePacking (G : SimpleGraph V) (T : Set (Finset V)) : Prop :=
  (∀ t ∈ T, G.IsNClique 3 t) ∧
    ∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ → ((t₁ : Set V) ∩ (t₂ : Set V)).ncard ≤ 1

/-- The **triangle covering number** `τ(G)`: the least number of edges meeting every triangle
of `G`. -/
noncomputable def triangleCoverNumber (G : SimpleGraph V) : ℕ :=
  sInf {n | ∃ C : Set (Sym2 V), IsTriangleCover G C ∧ C.ncard = n}

/-- The **triangle packing number** `ν(G)`: the greatest number of pairwise edge-disjoint
triangles of `G`. -/
noncomputable def trianglePackingNumber (G : SimpleGraph V) : ℕ :=
  sSup {n | ∃ T : Set (Finset V), IsTrianglePacking G T ∧ T.ncard = n}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) < 66 / 23 * trianglePackingNumber G

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) < 66 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) < 66 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) < 66 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) < 66 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) < 66 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) < 66 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) < 66 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 67 / 23 * trianglePackingNumber G

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 67 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 67 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 67 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 67 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 67 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 67 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 67 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 67 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 67 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 67 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 67 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 67 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 67 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 67 / 23 * trianglePackingNumber G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≥ 66 / 23 * trianglePackingNumber G

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≥ 66 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≥ 66 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≥ 66 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≥ 66 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≥ 66 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≥ 66 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≥ 66 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≥ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≥ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≥ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≥ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≥ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≥ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≥ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V), 66 / 23 * trianglePackingNumber G ≥ (triangleCoverNumber G : ℝ)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) :
    ((triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) ↔ (66 / 23 * trianglePackingNumber G ≥ (triangleCoverNumber G : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) :
    ((triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) ↔ (66 / 23 * trianglePackingNumber G ≥ (triangleCoverNumber G : ℝ)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) :
    ((triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) ↔ (66 / 23 * trianglePackingNumber G ≥ (triangleCoverNumber G : ℝ)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) :
    ((triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) ↔ (66 / 23 * trianglePackingNumber G ≥ (triangleCoverNumber G : ℝ)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) :
    ((triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) ↔ (66 / 23 * trianglePackingNumber G ≥ (triangleCoverNumber G : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) :
    ((triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) ↔ (66 / 23 * trianglePackingNumber G ≥ (triangleCoverNumber G : ℝ)) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) :
    ((triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) ↔ (66 / 23 * trianglePackingNumber G ≥ (triangleCoverNumber G : ℝ)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) :
    ((triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) ↔ (66 / 23 * trianglePackingNumber G ≥ (triangleCoverNumber G : ℝ)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) ↔
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), 66 / 23 * trianglePackingNumber G ≥ (triangleCoverNumber G : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) ↔
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), 66 / 23 * trianglePackingNumber G ≥ (triangleCoverNumber G : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) ↔
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), 66 / 23 * trianglePackingNumber G ≥ (triangleCoverNumber G : ℝ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) ↔
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), 66 / 23 * trianglePackingNumber G ≥ (triangleCoverNumber G : ℝ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V), 66 / 23 * trianglePackingNumber G > (triangleCoverNumber G : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), 66 / 23 * trianglePackingNumber G > (triangleCoverNumber G : ℝ)) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), 66 / 23 * trianglePackingNumber G > (triangleCoverNumber G : ℝ)) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), 66 / 23 * trianglePackingNumber G > (triangleCoverNumber G : ℝ)) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), 66 / 23 * trianglePackingNumber G > (triangleCoverNumber G : ℝ)) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), 66 / 23 * trianglePackingNumber G > (triangleCoverNumber G : ℝ)) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), 66 / 23 * trianglePackingNumber G > (triangleCoverNumber G : ℝ)) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), 66 / 23 * trianglePackingNumber G > (triangleCoverNumber G : ℝ)) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V), 67 / 23 * trianglePackingNumber G ≥ (triangleCoverNumber G : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), 67 / 23 * trianglePackingNumber G ≥ (triangleCoverNumber G : ℝ)) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), 67 / 23 * trianglePackingNumber G ≥ (triangleCoverNumber G : ℝ)) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), 67 / 23 * trianglePackingNumber G ≥ (triangleCoverNumber G : ℝ)) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), 67 / 23 * trianglePackingNumber G ≥ (triangleCoverNumber G : ℝ)) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), 67 / 23 * trianglePackingNumber G ≥ (triangleCoverNumber G : ℝ)) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), 67 / 23 * trianglePackingNumber G ≥ (triangleCoverNumber G : ℝ)) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), 67 / 23 * trianglePackingNumber G ≥ (triangleCoverNumber G : ℝ)) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), 67 / 23 * trianglePackingNumber G ≥ (triangleCoverNumber G : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), 67 / 23 * trianglePackingNumber G ≥ (triangleCoverNumber G : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), 67 / 23 * trianglePackingNumber G ≥ (triangleCoverNumber G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), 67 / 23 * trianglePackingNumber G ≥ (triangleCoverNumber G : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), 67 / 23 * trianglePackingNumber G ≥ (triangleCoverNumber G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), 67 / 23 * trianglePackingNumber G ≥ (triangleCoverNumber G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), 67 / 23 * trianglePackingNumber G ≥ (triangleCoverNumber G : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V), 66 / 23 * trianglePackingNumber G ≤ (triangleCoverNumber G : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), 66 / 23 * trianglePackingNumber G ≤ (triangleCoverNumber G : ℝ)) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), 66 / 23 * trianglePackingNumber G ≤ (triangleCoverNumber G : ℝ)) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), 66 / 23 * trianglePackingNumber G ≤ (triangleCoverNumber G : ℝ)) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), 66 / 23 * trianglePackingNumber G ≤ (triangleCoverNumber G : ℝ)) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), 66 / 23 * trianglePackingNumber G ≤ (triangleCoverNumber G : ℝ)) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), 66 / 23 * trianglePackingNumber G ≤ (triangleCoverNumber G : ℝ)) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), 66 / 23 * trianglePackingNumber G ≤ (triangleCoverNumber G : ℝ)) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), 66 / 23 * trianglePackingNumber G ≤ (triangleCoverNumber G : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), 66 / 23 * trianglePackingNumber G ≤ (triangleCoverNumber G : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), 66 / 23 * trianglePackingNumber G ≤ (triangleCoverNumber G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), 66 / 23 * trianglePackingNumber G ≤ (triangleCoverNumber G : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), 66 / 23 * trianglePackingNumber G ≤ (triangleCoverNumber G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), 66 / 23 * trianglePackingNumber G ≤ (triangleCoverNumber G : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), 66 / 23 * trianglePackingNumber G ≤ (triangleCoverNumber G : ℝ)) := by
  intro h; intros; aesop

#eval "FIN_CERTIFICAR"
