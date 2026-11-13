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

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l < m

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l < m) →
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l < m) →
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l < m) →
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l < m) →
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l < m) →
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l < m) →
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l < m) →
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l < m)) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l < m)) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l < m)) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l < m)) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l < m)) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l < m)) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l < m)) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l < m)) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l < m)) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l < m)) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l < m)) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l < m)) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l < m)) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l < m)) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l < m)) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l < m)) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l < m)) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l < m)) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l < m)) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l < m)) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l < m)) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l < m)) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l < m)) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l < m)) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l < m)) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l < m)) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l < m)) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l < m)) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l < m)) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l < m)) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l < m)) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l < m)) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l < m)) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l < m)) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l < m)) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l < m)) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l < m)) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l < m)) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l < m)) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l < m)) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l < m)) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l < m)) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l < m)) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l < m)) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l < m)) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l < m)) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l < m)) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l < m)) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l < m)) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l < m)) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l < m)) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l < m)) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l < m)) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l < m)) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l < m)) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l < m)) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l < m)) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l < m)) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l < m)) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l < m)) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l < m)) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l < m)) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l < m)) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l < m)) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≥ m

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≥ m) →
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≥ m) →
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≥ m) →
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≥ m) →
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≥ m) →
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≥ m) →
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≥ m) →
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) →
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≥ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) →
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≥ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) →
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≥ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) →
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≥ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) →
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≥ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) →
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≥ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) →
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≥ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l ≥ m)) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l ≥ m)) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l ≥ m)) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l ≥ m)) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l ≥ m)) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l ≥ m)) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l ≥ m)) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l ≥ m)) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l ≥ m)) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l ≥ m)) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l ≥ m)) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l ≥ m)) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l ≥ m)) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l ≥ m)) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l ≥ m)) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l ≥ m)) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l ≥ m)) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l ≥ m)) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l ≥ m)) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l ≥ m)) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l ≥ m)) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l ≥ m)) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l ≥ m)) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l ≥ m)) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l ≥ m)) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l ≥ m)) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l ≥ m)) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l ≥ m)) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l ≥ m)) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l ≥ m)) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l ≥ m)) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(forcingNumber n k l ≥ m)) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l ≥ m)) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l ≥ m)) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l ≥ m)) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l ≥ m)) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l ≥ m)) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l ≥ m)) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l ≥ m)) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l ≥ m)) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l ≥ m)) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l ≥ m)) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l ≥ m)) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l ≥ m)) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l ≥ m)) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l ≥ m)) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l ≥ m)) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l ≥ m)) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l ≥ m)) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l ≥ m)) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l ≥ m)) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l ≥ m)) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l ≥ m)) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l ≥ m)) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l ≥ m)) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l ≥ m)) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l ≥ m)) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l ≥ m)) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l ≥ m)) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l ≥ m)) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l ≥ m)) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l ≥ m)) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l ≥ m)) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (forcingNumber n k l ≥ m)) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), m ≥ forcingNumber n k l

set_option maxHeartbeats 200000 in
example {n k l m : ℕ} :
    (forcingNumber n k l ≤ m) ↔ (m ≥ forcingNumber n k l) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n k l m : ℕ} :
    (forcingNumber n k l ≤ m) ↔ (m ≥ forcingNumber n k l) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n k l m : ℕ} :
    (forcingNumber n k l ≤ m) ↔ (m ≥ forcingNumber n k l) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n k l m : ℕ} :
    (forcingNumber n k l ≤ m) ↔ (m ≥ forcingNumber n k l) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n k l m : ℕ} :
    (forcingNumber n k l ≤ m) ↔ (m ≥ forcingNumber n k l) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n k l m : ℕ} :
    (forcingNumber n k l ≤ m) ↔ (m ≥ forcingNumber n k l) := by
  omega

set_option maxHeartbeats 200000 in
example {n k l m : ℕ} :
    (forcingNumber n k l ≤ m) ↔ (m ≥ forcingNumber n k l) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n k l m : ℕ} :
    (forcingNumber n k l ≤ m) ↔ (m ≥ forcingNumber n k l) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) ↔
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), m ≥ forcingNumber n k l) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) ↔
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), m ≥ forcingNumber n k l) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) ↔
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), m ≥ forcingNumber n k l) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) ↔
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), m ≥ forcingNumber n k l) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n k l m : ℕ} (h₀ : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) ↔
    (∀ {n k l m : ℕ} (h₀ : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) ↔
    (∀ {n k l m : ℕ} (h₀ : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) ↔
    (∀ {n k l m : ℕ} (h₀ : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) ↔
    (∀ {n k l m : ℕ} (h₀ : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), ¬(m < forcingNumber n k l)

set_option maxHeartbeats 200000 in
example {n k l m : ℕ} :
    (forcingNumber n k l ≤ m) ↔ (¬(m < forcingNumber n k l)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n k l m : ℕ} :
    (forcingNumber n k l ≤ m) ↔ (¬(m < forcingNumber n k l)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n k l m : ℕ} :
    (forcingNumber n k l ≤ m) ↔ (¬(m < forcingNumber n k l)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n k l m : ℕ} :
    (forcingNumber n k l ≤ m) ↔ (¬(m < forcingNumber n k l)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n k l m : ℕ} :
    (forcingNumber n k l ≤ m) ↔ (¬(m < forcingNumber n k l)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n k l m : ℕ} :
    (forcingNumber n k l ≤ m) ↔ (¬(m < forcingNumber n k l)) := by
  omega

set_option maxHeartbeats 200000 in
example {n k l m : ℕ} :
    (forcingNumber n k l ≤ m) ↔ (¬(m < forcingNumber n k l)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n k l m : ℕ} :
    (forcingNumber n k l ≤ m) ↔ (¬(m < forcingNumber n k l)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) ↔
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), ¬(m < forcingNumber n k l)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) ↔
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), ¬(m < forcingNumber n k l)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) ↔
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), ¬(m < forcingNumber n k l)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) ↔
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), ¬(m < forcingNumber n k l)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), m > forcingNumber n k l

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), m > forcingNumber n k l) →
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), m > forcingNumber n k l) →
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), m > forcingNumber n k l) →
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), m > forcingNumber n k l) →
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), m > forcingNumber n k l) →
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), m > forcingNumber n k l) →
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), m > forcingNumber n k l) →
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m > forcingNumber n k l)) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m > forcingNumber n k l)) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m > forcingNumber n k l)) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m > forcingNumber n k l)) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m > forcingNumber n k l)) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m > forcingNumber n k l)) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m > forcingNumber n k l)) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m > forcingNumber n k l)) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m > forcingNumber n k l)) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m > forcingNumber n k l)) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m > forcingNumber n k l)) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m > forcingNumber n k l)) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m > forcingNumber n k l)) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m > forcingNumber n k l)) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m > forcingNumber n k l)) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m > forcingNumber n k l)) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m > forcingNumber n k l)) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m > forcingNumber n k l)) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m > forcingNumber n k l)) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m > forcingNumber n k l)) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m > forcingNumber n k l)) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m > forcingNumber n k l)) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m > forcingNumber n k l)) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m > forcingNumber n k l)) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m > forcingNumber n k l)) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m > forcingNumber n k l)) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m > forcingNumber n k l)) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m > forcingNumber n k l)) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m > forcingNumber n k l)) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m > forcingNumber n k l)) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m > forcingNumber n k l)) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m > forcingNumber n k l)) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m > forcingNumber n k l)) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m > forcingNumber n k l)) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m > forcingNumber n k l)) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m > forcingNumber n k l)) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m > forcingNumber n k l)) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m > forcingNumber n k l)) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m > forcingNumber n k l)) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m > forcingNumber n k l)) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m > forcingNumber n k l)) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m > forcingNumber n k l)) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m > forcingNumber n k l)) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m > forcingNumber n k l)) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m > forcingNumber n k l)) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m > forcingNumber n k l)) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m > forcingNumber n k l)) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m > forcingNumber n k l)) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m > forcingNumber n k l)) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m > forcingNumber n k l)) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m > forcingNumber n k l)) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m > forcingNumber n k l)) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m > forcingNumber n k l)) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m > forcingNumber n k l)) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m > forcingNumber n k l)) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m > forcingNumber n k l)) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m > forcingNumber n k l)) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m > forcingNumber n k l)) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m > forcingNumber n k l)) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m > forcingNumber n k l)) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m > forcingNumber n k l)) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m > forcingNumber n k l)) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m > forcingNumber n k l)) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m > forcingNumber n k l)) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), m ≤ forcingNumber n k l

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), m ≤ forcingNumber n k l) →
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), m ≤ forcingNumber n k l) →
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), m ≤ forcingNumber n k l) →
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), m ≤ forcingNumber n k l) →
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), m ≤ forcingNumber n k l) →
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), m ≤ forcingNumber n k l) →
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), m ≤ forcingNumber n k l) →
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) →
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), m ≤ forcingNumber n k l) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) →
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), m ≤ forcingNumber n k l) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) →
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), m ≤ forcingNumber n k l) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) →
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), m ≤ forcingNumber n k l) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) →
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), m ≤ forcingNumber n k l) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) →
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), m ≤ forcingNumber n k l) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), forcingNumber n k l ≤ m) →
    (∀ {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G), m ≤ forcingNumber n k l) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m ≤ forcingNumber n k l)) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m ≤ forcingNumber n k l)) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m ≤ forcingNumber n k l)) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m ≤ forcingNumber n k l)) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m ≤ forcingNumber n k l)) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m ≤ forcingNumber n k l)) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m ≤ forcingNumber n k l)) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m ≤ forcingNumber n k l)) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m ≤ forcingNumber n k l)) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m ≤ forcingNumber n k l)) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m ≤ forcingNumber n k l)) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m ≤ forcingNumber n k l)) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m ≤ forcingNumber n k l)) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m ≤ forcingNumber n k l)) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m ≤ forcingNumber n k l)) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m ≤ forcingNumber n k l)) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m ≤ forcingNumber n k l)) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m ≤ forcingNumber n k l)) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m ≤ forcingNumber n k l)) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m ≤ forcingNumber n k l)) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m ≤ forcingNumber n k l)) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m ≤ forcingNumber n k l)) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m ≤ forcingNumber n k l)) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m ≤ forcingNumber n k l)) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m ≤ forcingNumber n k l)) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m ≤ forcingNumber n k l)) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m ≤ forcingNumber n k l)) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m ≤ forcingNumber n k l)) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m ≤ forcingNumber n k l)) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m ≤ forcingNumber n k l)) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m ≤ forcingNumber n k l)) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), (∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) ∧ (¬(m ≤ forcingNumber n k l)) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m ≤ forcingNumber n k l)) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m ≤ forcingNumber n k l)) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m ≤ forcingNumber n k l)) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m ≤ forcingNumber n k l)) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m ≤ forcingNumber n k l)) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m ≤ forcingNumber n k l)) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m ≤ forcingNumber n k l)) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m ≤ forcingNumber n k l)) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m ≤ forcingNumber n k l)) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m ≤ forcingNumber n k l)) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m ≤ forcingNumber n k l)) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m ≤ forcingNumber n k l)) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m ≤ forcingNumber n k l)) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m ≤ forcingNumber n k l)) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m ≤ forcingNumber n k l)) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m ≤ forcingNumber n k l)) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m ≤ forcingNumber n k l)) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m ≤ forcingNumber n k l)) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m ≤ forcingNumber n k l)) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m ≤ forcingNumber n k l)) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m ≤ forcingNumber n k l)) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m ≤ forcingNumber n k l)) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m ≤ forcingNumber n k l)) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m ≤ forcingNumber n k l)) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m ≤ forcingNumber n k l)) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m ≤ forcingNumber n k l)) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m ≤ forcingNumber n k l)) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m ≤ forcingNumber n k l)) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m ≤ forcingNumber n k l)) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m ≤ forcingNumber n k l)) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m ≤ forcingNumber n k l)) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (l : ℕ) (m : ℕ), ¬((forcingNumber n k l ≤ m) ↔ (m ≤ forcingNumber n k l)) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {n k l m : ℕ} (h : ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph (Fin k), H.edgeSet.ncard = l ∧ H ⊑ G) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
