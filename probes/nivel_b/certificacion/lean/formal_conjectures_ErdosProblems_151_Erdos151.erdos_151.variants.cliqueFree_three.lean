import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 151

*References:*
- [erdosproblems.com/151](https://www.erdosproblems.com/151)
- [Er88] Erdős, P., *Problems and results in combinatorial analysis and graph theory*.
  Discrete Math. (1988), 81-92.
- [EGT92] Erdős, P. and Gallai, T. and Tuza, Zs., *Covering the cliques of a graph with
  vertices*. Discrete Math. (1992), 279-289.
-/

section

namespace Erdos151

open SimpleGraph

variable {V : Type*}

/-- `s` is a maximal clique of `G` with at least two vertices. -/
def IsBigMaximalClique (G : SimpleGraph V) (s : Finset V) : Prop :=
  Maximal (fun t : Finset V ↦ G.IsClique (t : Set V)) s ∧ 2 ≤ s.card

/-- `T` meets every maximal clique of `G` with at least two vertices. -/
def IsCliqueTransversal (G : SimpleGraph V) (T : Finset V) : Prop :=
  ∀ s, IsBigMaximalClique G s → ∃ v ∈ s, v ∈ T

/-- The clique transversal number $\tau(G)$: the minimal number of vertices that meet every
maximal clique of `G` with at least two vertices. -/
noncomputable def cliqueTransversalNumber (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ T : Finset V, IsCliqueTransversal G T ∧ T.card = k}

/-- $H(n)$: the largest `k` such that every triangle-free graph on `n` vertices contains an
independent set on `k` vertices. -/
noncomputable def H (n : ℕ) : ℕ :=
  sSup {k | ∀ G : SimpleGraph (Fin n), G.CliqueFree 3 → ∃ s, G.IsNIndepSet k s}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G < n - H n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G < n - H n) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G < n - H n) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G < n - H n) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G < n - H n) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G < n - H n) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G < n - H n) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G < n - H n) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≥ n - H n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≥ n - H n) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≥ n - H n) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≥ n - H n) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≥ n - H n) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≥ n - H n) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≥ n - H n) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≥ n - H n) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≥ n - H n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≥ n - H n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≥ n - H n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≥ n - H n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≥ n - H n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≥ n - H n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≥ n - H n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), n - H n ≥ cliqueTransversalNumber G

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) :
    (cliqueTransversalNumber G ≤ n - H n) ↔ (n - H n ≥ cliqueTransversalNumber G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) :
    (cliqueTransversalNumber G ≤ n - H n) ↔ (n - H n ≥ cliqueTransversalNumber G) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) :
    (cliqueTransversalNumber G ≤ n - H n) ↔ (n - H n ≥ cliqueTransversalNumber G) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) :
    (cliqueTransversalNumber G ≤ n - H n) ↔ (n - H n ≥ cliqueTransversalNumber G) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) :
    (cliqueTransversalNumber G ≤ n - H n) ↔ (n - H n ≥ cliqueTransversalNumber G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) :
    (cliqueTransversalNumber G ≤ n - H n) ↔ (n - H n ≥ cliqueTransversalNumber G) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) :
    (cliqueTransversalNumber G ≤ n - H n) ↔ (n - H n ≥ cliqueTransversalNumber G) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) :
    (cliqueTransversalNumber G ≤ n - H n) ↔ (n - H n ≥ cliqueTransversalNumber G) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) ↔
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), n - H n ≥ cliqueTransversalNumber G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) ↔
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), n - H n ≥ cliqueTransversalNumber G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) ↔
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), n - H n ≥ cliqueTransversalNumber G) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) ↔
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), n - H n ≥ cliqueTransversalNumber G) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG₀ : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) ↔
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG₀ : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) ↔
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG₀ : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) ↔
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG₀ : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) ↔
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG₀ : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), n - H n > cliqueTransversalNumber G

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), n - H n > cliqueTransversalNumber G) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), n - H n > cliqueTransversalNumber G) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), n - H n > cliqueTransversalNumber G) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), n - H n > cliqueTransversalNumber G) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), n - H n > cliqueTransversalNumber G) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), n - H n > cliqueTransversalNumber G) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), n - H n > cliqueTransversalNumber G) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), n - H n ≤ cliqueTransversalNumber G

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), n - H n ≤ cliqueTransversalNumber G) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), n - H n ≤ cliqueTransversalNumber G) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), n - H n ≤ cliqueTransversalNumber G) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), n - H n ≤ cliqueTransversalNumber G) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), n - H n ≤ cliqueTransversalNumber G) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), n - H n ≤ cliqueTransversalNumber G) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), n - H n ≤ cliqueTransversalNumber G) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), n - H n ≤ cliqueTransversalNumber G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), n - H n ≤ cliqueTransversalNumber G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), n - H n ≤ cliqueTransversalNumber G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), n - H n ≤ cliqueTransversalNumber G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), n - H n ≤ cliqueTransversalNumber G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), n - H n ≤ cliqueTransversalNumber G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), cliqueTransversalNumber G ≤ n - H n) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3), n - H n ≤ cliqueTransversalNumber G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
