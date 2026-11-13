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
  ∀ {n k : ℕ} (hkn : k ≤ n), forcingNumber n k 0 = 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n k : ℕ} (hkn : k < n), forcingNumber n k 0 = 0

set_option maxHeartbeats 200000 in
example :
    (∀ {n k : ℕ} (hkn : k ≤ n), forcingNumber n k 0 = 0) →
    (∀ {n k : ℕ} (hkn : k < n), forcingNumber n k 0 = 0) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n k : ℕ} (hkn : k ≤ n), forcingNumber n k 0 = 0) →
    (∀ {n k : ℕ} (hkn : k < n), forcingNumber n k 0 = 0) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n k : ℕ} (hkn : k ≤ n), forcingNumber n k 0 = 0) →
    (∀ {n k : ℕ} (hkn : k < n), forcingNumber n k 0 = 0) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n k : ℕ} (hkn : k ≤ n), forcingNumber n k 0 = 0) →
    (∀ {n k : ℕ} (hkn : k < n), forcingNumber n k 0 = 0) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n k : ℕ} (hkn : k ≤ n), forcingNumber n k 0 = 0) →
    (∀ {n k : ℕ} (hkn : k < n), forcingNumber n k 0 = 0) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n k : ℕ} (hkn : k ≤ n), forcingNumber n k 0 = 0) →
    (∀ {n k : ℕ} (hkn : k < n), forcingNumber n k 0 = 0) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n k : ℕ} (hkn : k ≤ n), forcingNumber n k 0 = 0) →
    (∀ {n k : ℕ} (hkn : k < n), forcingNumber n k 0 = 0) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n k : ℕ}  :
    (k ≤ n) ↔ (k < n) := by
  omega

set_option maxHeartbeats 200000 in
example {n k : ℕ}  :
    (k ≤ n) ↔ (k < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n k : ℕ}  :
    (k ≤ n) ↔ (k < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n k : ℕ}  :
    (k ≤ n) ↔ (k < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n k : ℕ}  :
    (k ≤ n) ↔ (k < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n k : ℕ}  :
    (k ≤ n) ↔ (k < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n k : ℕ}  :
    (k ≤ n) ↔ (k < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (k < n))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (k < n))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (k < n))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (k < n))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (k < n))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (k < n))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (k < n))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (k < n))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (k < n))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (k < n))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (k < n))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (k < n))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (k < n))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (k < n))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (k < n))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (k < n))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (k < n))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (k < n))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (k < n))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (k < n))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (k < n))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (k < n))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (k < n))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (k < n))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (k < n))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (k < n))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (k < n))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (k < n))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (k < n))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (k < n))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (k < n))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (k < n))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (k < n)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (k < n)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (k < n)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (k < n)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (k < n)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (k < n)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (k < n)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (k < n)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (k < n)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (k < n)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (k < n)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (k < n)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (k < n)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (k < n)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (k < n)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (k < n)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (k < n)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (k < n)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (k < n)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (k < n)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (k < n)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (k < n)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (k < n)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (k < n)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (k < n)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (k < n)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (k < n)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (k < n)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (k < n)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (k < n)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (k < n)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (k < n)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n k : ℕ} (hkn : k ≤ n), forcingNumber n k 0 = 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n k : ℕ} (hkn : n ≥ k), forcingNumber n k 0 = 0

set_option maxHeartbeats 200000 in
example {n k : ℕ} :
    (k ≤ n) ↔ (n ≥ k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n k : ℕ} :
    (k ≤ n) ↔ (n ≥ k) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n k : ℕ} :
    (k ≤ n) ↔ (n ≥ k) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n k : ℕ} :
    (k ≤ n) ↔ (n ≥ k) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n k : ℕ} :
    (k ≤ n) ↔ (n ≥ k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n k : ℕ} :
    (k ≤ n) ↔ (n ≥ k) := by
  omega

set_option maxHeartbeats 200000 in
example {n k : ℕ} :
    (k ≤ n) ↔ (n ≥ k) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n k : ℕ} :
    (k ≤ n) ↔ (n ≥ k) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n k : ℕ} (hkn : k ≤ n), forcingNumber n k 0 = 0) ↔
    (∀ {n k : ℕ} (hkn : n ≥ k), forcingNumber n k 0 = 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n k : ℕ} (hkn : k ≤ n), forcingNumber n k 0 = 0) ↔
    (∀ {n k : ℕ} (hkn : n ≥ k), forcingNumber n k 0 = 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n k : ℕ} (hkn : k ≤ n), forcingNumber n k 0 = 0) ↔
    (∀ {n k : ℕ} (hkn : n ≥ k), forcingNumber n k 0 = 0) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n k : ℕ} (hkn : k ≤ n), forcingNumber n k 0 = 0) ↔
    (∀ {n k : ℕ} (hkn : n ≥ k), forcingNumber n k 0 = 0) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n k : ℕ} (hkn : k ≤ n), forcingNumber n k 0 = 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n k : ℕ} (hkn₀ : k ≤ n), forcingNumber n k 0 = 0

set_option maxHeartbeats 200000 in
example :
    (∀ {n k : ℕ} (hkn : k ≤ n), forcingNumber n k 0 = 0) ↔
    (∀ {n k : ℕ} (hkn₀ : k ≤ n), forcingNumber n k 0 = 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n k : ℕ} (hkn : k ≤ n), forcingNumber n k 0 = 0) ↔
    (∀ {n k : ℕ} (hkn₀ : k ≤ n), forcingNumber n k 0 = 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n k : ℕ} (hkn : k ≤ n), forcingNumber n k 0 = 0) ↔
    (∀ {n k : ℕ} (hkn₀ : k ≤ n), forcingNumber n k 0 = 0) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n k : ℕ} (hkn : k ≤ n), forcingNumber n k 0 = 0) ↔
    (∀ {n k : ℕ} (hkn₀ : k ≤ n), forcingNumber n k 0 = 0) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n k : ℕ} (hkn : k ≤ n), forcingNumber n k 0 = 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n k : ℕ} (hkn : ¬(n < k)), forcingNumber n k 0 = 0

set_option maxHeartbeats 200000 in
example {n k : ℕ} :
    (k ≤ n) ↔ (¬(n < k)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n k : ℕ} :
    (k ≤ n) ↔ (¬(n < k)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n k : ℕ} :
    (k ≤ n) ↔ (¬(n < k)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n k : ℕ} :
    (k ≤ n) ↔ (¬(n < k)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n k : ℕ} :
    (k ≤ n) ↔ (¬(n < k)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n k : ℕ} :
    (k ≤ n) ↔ (¬(n < k)) := by
  omega

set_option maxHeartbeats 200000 in
example {n k : ℕ} :
    (k ≤ n) ↔ (¬(n < k)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n k : ℕ} :
    (k ≤ n) ↔ (¬(n < k)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n k : ℕ} (hkn : k ≤ n), forcingNumber n k 0 = 0) ↔
    (∀ {n k : ℕ} (hkn : ¬(n < k)), forcingNumber n k 0 = 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n k : ℕ} (hkn : k ≤ n), forcingNumber n k 0 = 0) ↔
    (∀ {n k : ℕ} (hkn : ¬(n < k)), forcingNumber n k 0 = 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n k : ℕ} (hkn : k ≤ n), forcingNumber n k 0 = 0) ↔
    (∀ {n k : ℕ} (hkn : ¬(n < k)), forcingNumber n k 0 = 0) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n k : ℕ} (hkn : k ≤ n), forcingNumber n k 0 = 0) ↔
    (∀ {n k : ℕ} (hkn : ¬(n < k)), forcingNumber n k 0 = 0) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n k : ℕ} (hkn : k ≤ n), forcingNumber n k 0 = 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n k : ℕ} (hkn : n > k), forcingNumber n k 0 = 0

set_option maxHeartbeats 200000 in
example :
    (∀ {n k : ℕ} (hkn : k ≤ n), forcingNumber n k 0 = 0) →
    (∀ {n k : ℕ} (hkn : n > k), forcingNumber n k 0 = 0) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n k : ℕ} (hkn : k ≤ n), forcingNumber n k 0 = 0) →
    (∀ {n k : ℕ} (hkn : n > k), forcingNumber n k 0 = 0) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n k : ℕ} (hkn : k ≤ n), forcingNumber n k 0 = 0) →
    (∀ {n k : ℕ} (hkn : n > k), forcingNumber n k 0 = 0) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n k : ℕ} (hkn : k ≤ n), forcingNumber n k 0 = 0) →
    (∀ {n k : ℕ} (hkn : n > k), forcingNumber n k 0 = 0) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n k : ℕ} (hkn : k ≤ n), forcingNumber n k 0 = 0) →
    (∀ {n k : ℕ} (hkn : n > k), forcingNumber n k 0 = 0) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n k : ℕ} (hkn : k ≤ n), forcingNumber n k 0 = 0) →
    (∀ {n k : ℕ} (hkn : n > k), forcingNumber n k 0 = 0) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n k : ℕ} (hkn : k ≤ n), forcingNumber n k 0 = 0) →
    (∀ {n k : ℕ} (hkn : n > k), forcingNumber n k 0 = 0) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n k : ℕ}  :
    (k ≤ n) ↔ (n > k) := by
  omega

set_option maxHeartbeats 200000 in
example {n k : ℕ}  :
    (k ≤ n) ↔ (n > k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n k : ℕ}  :
    (k ≤ n) ↔ (n > k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n k : ℕ}  :
    (k ≤ n) ↔ (n > k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n k : ℕ}  :
    (k ≤ n) ↔ (n > k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n k : ℕ}  :
    (k ≤ n) ↔ (n > k) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n k : ℕ}  :
    (k ≤ n) ↔ (n > k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (n > k))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (n > k))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (n > k))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (n > k))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (n > k))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (n > k))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (n > k))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (n > k))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (n > k))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (n > k))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (n > k))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (n > k))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (n > k))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (n > k))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (n > k))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (n > k))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (n > k))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (n > k))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (n > k))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (n > k))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (n > k))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (n > k))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (n > k))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (n > k))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (n > k))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (n > k))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (n > k))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (n > k))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (n > k))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (n > k))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (n > k))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (¬((k ≤ n) ↔ (n > k))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (n > k)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (n > k)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (n > k)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (n > k)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (n > k)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (n > k)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (n > k)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (n > k)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (n > k)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (n > k)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (n > k)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (n > k)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (n > k)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (n > k)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (n > k)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (n > k)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (n > k)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (n > k)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (n > k)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (n > k)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (n > k)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (n > k)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (n > k)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (n > k)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (n > k)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (n > k)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (n > k)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (n > k)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (n > k)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (n > k)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (n > k)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (n > k)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {n k : ℕ} (hkn : k ≤ n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {n k : ℕ} (hkn : k ≤ n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {n k : ℕ} (hkn : k ≤ n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {n k : ℕ} (hkn : k ≤ n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {n k : ℕ} (hkn : k ≤ n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
