import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 717

*References:*
- [erdosproblems.com/717](https://www.erdosproblems.com/717)
- [ErFa81] Erdős, Paul and Fajtlowicz, Siemion, *On the conjecture of Hajós*. Combinatorica 1
  (1981), 141-143. [PDF](https://www.renyi.hu/~p_erdos/1981-17.pdf)
- [FLS13] Fox, Jacob and Lee, Choongbum and Sudakov, Benny, *Chromatic number, clique
  subdivisions, and the conjectures of Hajós and Erdős-Fajtlowicz*. Combinatorica 33 (2013),
  181-197. [arXiv:1107.1920](https://arxiv.org/abs/1107.1920)
-/

section

open Filter Topology

namespace Erdos717

/-- The edges of $K_r$ on `Fin r`, each written as a pair `(i, j)` with `i < j`. -/
abbrev CliqueEdge (r : ℕ) := {e : Fin r × Fin r // e.1 < e.2}

/-- The vertices of a walk other than its two endpoints. -/
def walkInteriorSet {V : Type*} {G : SimpleGraph V} {u v : V} (p : G.Walk u v) : Set V :=
  {x | x ∈ p.support ∧ x ≠ u ∧ x ≠ v}

/--
A subdivision of the complete graph $K_r$ in `G`: `r` distinct branch vertices, and for each
edge `(i, j)` of $K_r$ a path in `G` from the `i`th to the `j`th branch vertex. The interiors of
these paths are pairwise disjoint and contain no branch vertex.
-/
structure CliqueSubdivision {V : Type*} (G : SimpleGraph V) (r : ℕ) where
  branch : Fin r ↪ V
  path : ∀ e : CliqueEdge r, G.Walk (branch e.1.1) (branch e.1.2)
  path_isPath : ∀ e, (path e).IsPath
  interior_avoids_branch : ∀ e, Disjoint (walkInteriorSet (path e)) (Set.range branch)
  interior_pairwise : Pairwise fun e f =>
    Disjoint (walkInteriorSet (path e)) (walkInteriorSet (path f))

/-- `G` contains a subdivision of the complete graph $K_r$. -/
def ContainsCliqueSubdivision {V : Type*} (G : SimpleGraph V) (r : ℕ) : Prop :=
  Nonempty (CliqueSubdivision G r)

open scoped Classical in
/--
$\sigma(G)$: the largest `r` such that `G` contains a subdivision of $K_r$.

A subdivision of $K_r$ has `r` distinct branch vertices, so it is enough to search `r ≤ |V|`.
Every graph contains a subdivision of $K_0$, so $\sigma(G) = 0$ only if `V` is empty.
-/
noncomputable def cliqueSubdivisionNumber {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  Nat.findGreatest (ContainsCliqueSubdivision G) (Fintype.card V)

universe u_c1 u_c2 u_c3 u_c4 u_c5 u_c6 u_c7 u_c8 u_c9 u_c10 u_c11 u_c12 u_c13 u_c14 u_c15 u_c16 u_c17 u_c18 u_c19
set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c1} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c2} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r < cliqueSubdivisionNumber G

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c2} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r < cliqueSubdivisionNumber G) →
    (∀ {V : Type u_c1} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c2} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r < cliqueSubdivisionNumber G) →
    (∀ {V : Type u_c1} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c2} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r < cliqueSubdivisionNumber G) →
    (∀ {V : Type u_c1} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c2} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r < cliqueSubdivisionNumber G) →
    (∀ {V : Type u_c1} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c2} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r < cliqueSubdivisionNumber G) →
    (∀ {V : Type u_c1} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c2} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r < cliqueSubdivisionNumber G) →
    (∀ {V : Type u_c1} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c2} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r < cliqueSubdivisionNumber G) →
    (∀ {V : Type u_c1} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c4} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c5} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≥ cliqueSubdivisionNumber G

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c5} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≥ cliqueSubdivisionNumber G) →
    (∀ {V : Type u_c4} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c5} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≥ cliqueSubdivisionNumber G) →
    (∀ {V : Type u_c4} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c5} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≥ cliqueSubdivisionNumber G) →
    (∀ {V : Type u_c4} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c5} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≥ cliqueSubdivisionNumber G) →
    (∀ {V : Type u_c4} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c5} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≥ cliqueSubdivisionNumber G) →
    (∀ {V : Type u_c4} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c5} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≥ cliqueSubdivisionNumber G) →
    (∀ {V : Type u_c4} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c5} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≥ cliqueSubdivisionNumber G) →
    (∀ {V : Type u_c4} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c4} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) →
    (∀ {V : Type u_c5} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≥ cliqueSubdivisionNumber G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c4} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) →
    (∀ {V : Type u_c5} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≥ cliqueSubdivisionNumber G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c4} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) →
    (∀ {V : Type u_c5} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≥ cliqueSubdivisionNumber G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c4} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) →
    (∀ {V : Type u_c5} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≥ cliqueSubdivisionNumber G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c4} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) →
    (∀ {V : Type u_c5} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≥ cliqueSubdivisionNumber G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c4} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) →
    (∀ {V : Type u_c5} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≥ cliqueSubdivisionNumber G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c4} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) →
    (∀ {V : Type u_c5} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≥ cliqueSubdivisionNumber G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c7} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c8} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), cliqueSubdivisionNumber G ≥ r

set_option maxHeartbeats 200000 in
example {V : Type u_c9} [Fintype V] {G : SimpleGraph V} {r : ℕ} :
    (r ≤ cliqueSubdivisionNumber G) ↔ (cliqueSubdivisionNumber G ≥ r) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {V : Type u_c9} [Fintype V] {G : SimpleGraph V} {r : ℕ} :
    (r ≤ cliqueSubdivisionNumber G) ↔ (cliqueSubdivisionNumber G ≥ r) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {V : Type u_c9} [Fintype V] {G : SimpleGraph V} {r : ℕ} :
    (r ≤ cliqueSubdivisionNumber G) ↔ (cliqueSubdivisionNumber G ≥ r) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {V : Type u_c9} [Fintype V] {G : SimpleGraph V} {r : ℕ} :
    (r ≤ cliqueSubdivisionNumber G) ↔ (cliqueSubdivisionNumber G ≥ r) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {V : Type u_c9} [Fintype V] {G : SimpleGraph V} {r : ℕ} :
    (r ≤ cliqueSubdivisionNumber G) ↔ (cliqueSubdivisionNumber G ≥ r) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {V : Type u_c9} [Fintype V] {G : SimpleGraph V} {r : ℕ} :
    (r ≤ cliqueSubdivisionNumber G) ↔ (cliqueSubdivisionNumber G ≥ r) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type u_c9} [Fintype V] {G : SimpleGraph V} {r : ℕ} :
    (r ≤ cliqueSubdivisionNumber G) ↔ (cliqueSubdivisionNumber G ≥ r) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {V : Type u_c9} [Fintype V] {G : SimpleGraph V} {r : ℕ} :
    (r ≤ cliqueSubdivisionNumber G) ↔ (cliqueSubdivisionNumber G ≥ r) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c7} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) ↔
    (∀ {V : Type u_c8} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), cliqueSubdivisionNumber G ≥ r) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c7} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) ↔
    (∀ {V : Type u_c8} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), cliqueSubdivisionNumber G ≥ r) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c7} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) ↔
    (∀ {V : Type u_c8} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), cliqueSubdivisionNumber G ≥ r) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c7} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) ↔
    (∀ {V : Type u_c8} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), cliqueSubdivisionNumber G ≥ r) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c10} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c11} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h₀ : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c10} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) ↔
    (∀ {V : Type u_c11} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h₀ : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c10} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) ↔
    (∀ {V : Type u_c11} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h₀ : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c10} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) ↔
    (∀ {V : Type u_c11} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h₀ : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c10} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) ↔
    (∀ {V : Type u_c11} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h₀ : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c13} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c14} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), cliqueSubdivisionNumber G > r

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c14} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), cliqueSubdivisionNumber G > r) →
    (∀ {V : Type u_c13} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c14} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), cliqueSubdivisionNumber G > r) →
    (∀ {V : Type u_c13} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c14} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), cliqueSubdivisionNumber G > r) →
    (∀ {V : Type u_c13} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c14} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), cliqueSubdivisionNumber G > r) →
    (∀ {V : Type u_c13} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c14} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), cliqueSubdivisionNumber G > r) →
    (∀ {V : Type u_c13} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c14} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), cliqueSubdivisionNumber G > r) →
    (∀ {V : Type u_c13} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c14} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), cliqueSubdivisionNumber G > r) →
    (∀ {V : Type u_c13} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c16} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c17} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), cliqueSubdivisionNumber G ≤ r

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c17} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), cliqueSubdivisionNumber G ≤ r) →
    (∀ {V : Type u_c16} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c17} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), cliqueSubdivisionNumber G ≤ r) →
    (∀ {V : Type u_c16} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c17} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), cliqueSubdivisionNumber G ≤ r) →
    (∀ {V : Type u_c16} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c17} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), cliqueSubdivisionNumber G ≤ r) →
    (∀ {V : Type u_c16} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c17} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), cliqueSubdivisionNumber G ≤ r) →
    (∀ {V : Type u_c16} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c17} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), cliqueSubdivisionNumber G ≤ r) →
    (∀ {V : Type u_c16} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c17} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), cliqueSubdivisionNumber G ≤ r) →
    (∀ {V : Type u_c16} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c16} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) →
    (∀ {V : Type u_c17} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), cliqueSubdivisionNumber G ≤ r) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c16} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) →
    (∀ {V : Type u_c17} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), cliqueSubdivisionNumber G ≤ r) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c16} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) →
    (∀ {V : Type u_c17} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), cliqueSubdivisionNumber G ≤ r) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c16} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) →
    (∀ {V : Type u_c17} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), cliqueSubdivisionNumber G ≤ r) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c16} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) →
    (∀ {V : Type u_c17} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), cliqueSubdivisionNumber G ≤ r) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c16} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) →
    (∀ {V : Type u_c17} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), cliqueSubdivisionNumber G ≤ r) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c16} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), r ≤ cliqueSubdivisionNumber G) →
    (∀ {V : Type u_c17} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r), cliqueSubdivisionNumber G ≤ r) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type u_c19} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {V : Type u_c19} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type u_c19} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {V : Type u_c19} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type u_c19} [Fintype V] {G : SimpleGraph V} {r : ℕ} (h : ContainsCliqueSubdivision G r) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
