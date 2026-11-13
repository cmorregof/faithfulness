import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 626

*References:*
- [erdosproblems.com/626](https://www.erdosproblems.com/626)
- [Er59b] Erdős, P., *Graph theory and probability*. Canadian J. Math. (1959), 34-38.
- [Er62b] Erdős, P., *On circuits and subgraphs of chromatic graphs*. Mathematika (1962),
  170-175.
- [Er69b] Erdős, P., *Problems and results in chromatic graph theory*. Proof Techniques in Graph
  Theory (Proc. Second Ann Arbor Graph Theory Conf., Ann Arbor, Mich., 1968) (1969), 27-35.
- [Ko88] Kostochka, A. V., *Upper bounds on the chromatic number of graphs*. Trudy Inst. Mat.
  (Novosibirsk) (1988), 204-226, 265.
-/

section

open Filter
open scoped Topology

namespace Erdos626

/--
`g k n` is $g_k(n)$: the largest $m$ such that some graph on $n$ vertices has chromatic number
exactly $k$ and girth $> m$, that is, no cycle of length $\leq m$.

The girth is `SimpleGraph.egirth`, which is `⊤` for an acyclic graph. The value `sSup ∅ = 0`
for $n < k$ affects only finitely many $n$. For $k \leq 2$ the set is unbounded whenever an
acyclic graph on $n$ vertices with chromatic number $k$ exists, and then `sSup` is also $0$; this
case is not used below, where $k \geq 4$.
-/
noncomputable def g (k n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ G : SimpleGraph (Fin n), G.chromaticNumber = k ∧ (m : ℕ∞) < G.egirth}

/--
`h m n` is $h^{(m)}(n)$: the largest chromatic number of a graph on $n$ vertices with girth
$> m$.
-/
noncomputable def h (m n : ℕ) : ℕ :=
  sSup {c : ℕ | ∃ G : SimpleGraph (Fin n), (m : ℕ∞) < G.egirth ∧ G.chromaticNumber = c}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m n : ℕ) (hm : m ≤ 2), h m n = n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m n : ℕ) (hm : m < 2), h m n = n

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) →
    (∀ (m n : ℕ) (hm : m < 2), h m n = n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) →
    (∀ (m n : ℕ) (hm : m < 2), h m n = n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) →
    (∀ (m n : ℕ) (hm : m < 2), h m n = n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) →
    (∀ (m n : ℕ) (hm : m < 2), h m n = n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) →
    (∀ (m n : ℕ) (hm : m < 2), h m n = n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) →
    (∀ (m n : ℕ) (hm : m < 2), h m n = n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) →
    (∀ (m n : ℕ) (hm : m < 2), h m n = n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (m n : ℕ)  :
    (m ≤ 2) ↔ (m < 2) := by
  omega

set_option maxHeartbeats 200000 in
example (m n : ℕ)  :
    (m ≤ 2) ↔ (m < 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (m n : ℕ)  :
    (m ≤ 2) ↔ (m < 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (m n : ℕ)  :
    (m ≤ 2) ↔ (m < 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (m n : ℕ)  :
    (m ≤ 2) ↔ (m < 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (m n : ℕ)  :
    (m ≤ 2) ↔ (m < 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example (m n : ℕ)  :
    (m ≤ 2) ↔ (m < 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((m ≤ 2) ↔ (m < 2))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((m ≤ 2) ↔ (m < 2))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((m ≤ 2) ↔ (m < 2))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((m ≤ 2) ↔ (m < 2))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((m ≤ 2) ↔ (m < 2))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((m ≤ 2) ↔ (m < 2))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((m ≤ 2) ↔ (m < 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((m ≤ 2) ↔ (m < 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((m ≤ 2) ↔ (m < 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((m ≤ 2) ↔ (m < 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((m ≤ 2) ↔ (m < 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((m ≤ 2) ↔ (m < 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m n : ℕ) (hm : m ≤ 2), h m n = n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m n : ℕ) (hm : m ≤ 3), h m n = n

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : m ≤ 3), h m n = n) →
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : m ≤ 3), h m n = n) →
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : m ≤ 3), h m n = n) →
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : m ≤ 3), h m n = n) →
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : m ≤ 3), h m n = n) →
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : m ≤ 3), h m n = n) →
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : m ≤ 3), h m n = n) →
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (m n : ℕ)  :
    (m ≤ 2) ↔ (m ≤ 3) := by
  omega

set_option maxHeartbeats 200000 in
example (m n : ℕ)  :
    (m ≤ 2) ↔ (m ≤ 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (m n : ℕ)  :
    (m ≤ 2) ↔ (m ≤ 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (m n : ℕ)  :
    (m ≤ 2) ↔ (m ≤ 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (m n : ℕ)  :
    (m ≤ 2) ↔ (m ≤ 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (m n : ℕ)  :
    (m ≤ 2) ↔ (m ≤ 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (m n : ℕ)  :
    (m ≤ 2) ↔ (m ≤ 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((m ≤ 2) ↔ (m ≤ 3))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((m ≤ 2) ↔ (m ≤ 3))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((m ≤ 2) ↔ (m ≤ 3))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((m ≤ 2) ↔ (m ≤ 3))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((m ≤ 2) ↔ (m ≤ 3))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((m ≤ 2) ↔ (m ≤ 3))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((m ≤ 2) ↔ (m ≤ 3))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((m ≤ 2) ↔ (m ≤ 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((m ≤ 2) ↔ (m ≤ 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((m ≤ 2) ↔ (m ≤ 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((m ≤ 2) ↔ (m ≤ 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((m ≤ 2) ↔ (m ≤ 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((m ≤ 2) ↔ (m ≤ 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((m ≤ 2) ↔ (m ≤ 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m n : ℕ) (hm : m ≤ 2), h m n = n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m n : ℕ) (hm : 2 ≥ m), h m n = n

set_option maxHeartbeats 200000 in
example (m n : ℕ) :
    (m ≤ 2) ↔ (2 ≥ m) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (m n : ℕ) :
    (m ≤ 2) ↔ (2 ≥ m) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (m n : ℕ) :
    (m ≤ 2) ↔ (2 ≥ m) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (m n : ℕ) :
    (m ≤ 2) ↔ (2 ≥ m) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (m n : ℕ) :
    (m ≤ 2) ↔ (2 ≥ m) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (m n : ℕ) :
    (m ≤ 2) ↔ (2 ≥ m) := by
  omega

set_option maxHeartbeats 200000 in
example (m n : ℕ) :
    (m ≤ 2) ↔ (2 ≥ m) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (m n : ℕ) :
    (m ≤ 2) ↔ (2 ≥ m) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) ↔
    (∀ (m n : ℕ) (hm : 2 ≥ m), h m n = n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) ↔
    (∀ (m n : ℕ) (hm : 2 ≥ m), h m n = n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) ↔
    (∀ (m n : ℕ) (hm : 2 ≥ m), h m n = n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) ↔
    (∀ (m n : ℕ) (hm : 2 ≥ m), h m n = n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m n : ℕ) (hm : m ≤ 2), h m n = n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m n : ℕ) (hm₀ : m ≤ 2), h m n = n

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) ↔
    (∀ (m n : ℕ) (hm₀ : m ≤ 2), h m n = n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) ↔
    (∀ (m n : ℕ) (hm₀ : m ≤ 2), h m n = n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) ↔
    (∀ (m n : ℕ) (hm₀ : m ≤ 2), h m n = n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) ↔
    (∀ (m n : ℕ) (hm₀ : m ≤ 2), h m n = n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m n : ℕ) (hm : m ≤ 2), h m n = n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m n : ℕ) (hm : ¬(2 < m)), h m n = n

set_option maxHeartbeats 200000 in
example (m n : ℕ) :
    (m ≤ 2) ↔ (¬(2 < m)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (m n : ℕ) :
    (m ≤ 2) ↔ (¬(2 < m)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (m n : ℕ) :
    (m ≤ 2) ↔ (¬(2 < m)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (m n : ℕ) :
    (m ≤ 2) ↔ (¬(2 < m)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (m n : ℕ) :
    (m ≤ 2) ↔ (¬(2 < m)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (m n : ℕ) :
    (m ≤ 2) ↔ (¬(2 < m)) := by
  omega

set_option maxHeartbeats 200000 in
example (m n : ℕ) :
    (m ≤ 2) ↔ (¬(2 < m)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (m n : ℕ) :
    (m ≤ 2) ↔ (¬(2 < m)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) ↔
    (∀ (m n : ℕ) (hm : ¬(2 < m)), h m n = n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) ↔
    (∀ (m n : ℕ) (hm : ¬(2 < m)), h m n = n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) ↔
    (∀ (m n : ℕ) (hm : ¬(2 < m)), h m n = n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) ↔
    (∀ (m n : ℕ) (hm : ¬(2 < m)), h m n = n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m n : ℕ) (hm : m ≤ 2), h m n = n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m n : ℕ) (hm : m < 3), h m n = n

set_option maxHeartbeats 200000 in
example (m n : ℕ) :
    (m ≤ 2) ↔ (m < 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (m n : ℕ) :
    (m ≤ 2) ↔ (m < 3) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (m n : ℕ) :
    (m ≤ 2) ↔ (m < 3) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (m n : ℕ) :
    (m ≤ 2) ↔ (m < 3) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (m n : ℕ) :
    (m ≤ 2) ↔ (m < 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (m n : ℕ) :
    (m ≤ 2) ↔ (m < 3) := by
  omega

set_option maxHeartbeats 200000 in
example (m n : ℕ) :
    (m ≤ 2) ↔ (m < 3) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (m n : ℕ) :
    (m ≤ 2) ↔ (m < 3) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) ↔
    (∀ (m n : ℕ) (hm : m < 3), h m n = n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) ↔
    (∀ (m n : ℕ) (hm : m < 3), h m n = n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) ↔
    (∀ (m n : ℕ) (hm : m < 3), h m n = n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) ↔
    (∀ (m n : ℕ) (hm : m < 3), h m n = n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m n : ℕ) (hm : m ≤ 2), h m n = n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m n : ℕ) (hm : 2 > m), h m n = n

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) →
    (∀ (m n : ℕ) (hm : 2 > m), h m n = n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) →
    (∀ (m n : ℕ) (hm : 2 > m), h m n = n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) →
    (∀ (m n : ℕ) (hm : 2 > m), h m n = n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) →
    (∀ (m n : ℕ) (hm : 2 > m), h m n = n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) →
    (∀ (m n : ℕ) (hm : 2 > m), h m n = n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) →
    (∀ (m n : ℕ) (hm : 2 > m), h m n = n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) →
    (∀ (m n : ℕ) (hm : 2 > m), h m n = n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (m n : ℕ)  :
    (m ≤ 2) ↔ (2 > m) := by
  omega

set_option maxHeartbeats 200000 in
example (m n : ℕ)  :
    (m ≤ 2) ↔ (2 > m) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (m n : ℕ)  :
    (m ≤ 2) ↔ (2 > m) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (m n : ℕ)  :
    (m ≤ 2) ↔ (2 > m) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (m n : ℕ)  :
    (m ≤ 2) ↔ (2 > m) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (m n : ℕ)  :
    (m ≤ 2) ↔ (2 > m) := by
  simp_all

set_option maxHeartbeats 200000 in
example (m n : ℕ)  :
    (m ≤ 2) ↔ (2 > m) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((m ≤ 2) ↔ (2 > m))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((m ≤ 2) ↔ (2 > m))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((m ≤ 2) ↔ (2 > m))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((m ≤ 2) ↔ (2 > m))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((m ≤ 2) ↔ (2 > m))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((m ≤ 2) ↔ (2 > m))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((m ≤ 2) ↔ (2 > m)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((m ≤ 2) ↔ (2 > m)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((m ≤ 2) ↔ (2 > m)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((m ≤ 2) ↔ (2 > m)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((m ≤ 2) ↔ (2 > m)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((m ≤ 2) ↔ (2 > m)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m n : ℕ) (hm : m ≤ 2), h m n = n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m n : ℕ) (hm : 3 ≥ m), h m n = n

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : 3 ≥ m), h m n = n) →
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : 3 ≥ m), h m n = n) →
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : 3 ≥ m), h m n = n) →
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : 3 ≥ m), h m n = n) →
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : 3 ≥ m), h m n = n) →
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : 3 ≥ m), h m n = n) →
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : 3 ≥ m), h m n = n) →
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (m n : ℕ)  :
    (m ≤ 2) ↔ (3 ≥ m) := by
  omega

set_option maxHeartbeats 200000 in
example (m n : ℕ)  :
    (m ≤ 2) ↔ (3 ≥ m) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (m n : ℕ)  :
    (m ≤ 2) ↔ (3 ≥ m) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (m n : ℕ)  :
    (m ≤ 2) ↔ (3 ≥ m) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (m n : ℕ)  :
    (m ≤ 2) ↔ (3 ≥ m) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (m n : ℕ)  :
    (m ≤ 2) ↔ (3 ≥ m) := by
  simp_all

set_option maxHeartbeats 200000 in
example (m n : ℕ)  :
    (m ≤ 2) ↔ (3 ≥ m) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((m ≤ 2) ↔ (3 ≥ m))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((m ≤ 2) ↔ (3 ≥ m))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((m ≤ 2) ↔ (3 ≥ m))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((m ≤ 2) ↔ (3 ≥ m))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((m ≤ 2) ↔ (3 ≥ m))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((m ≤ 2) ↔ (3 ≥ m))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((m ≤ 2) ↔ (3 ≥ m))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((m ≤ 2) ↔ (3 ≥ m)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((m ≤ 2) ↔ (3 ≥ m)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((m ≤ 2) ↔ (3 ≥ m)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((m ≤ 2) ↔ (3 ≥ m)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((m ≤ 2) ↔ (3 ≥ m)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((m ≤ 2) ↔ (3 ≥ m)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((m ≤ 2) ↔ (3 ≥ m)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m n : ℕ) (hm : m ≤ 2), h m n = n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m n : ℕ) (hm : m < 4), h m n = n

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : m < 4), h m n = n) →
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : m < 4), h m n = n) →
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : m < 4), h m n = n) →
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : m < 4), h m n = n) →
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : m < 4), h m n = n) →
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : m < 4), h m n = n) →
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m n : ℕ) (hm : m < 4), h m n = n) →
    (∀ (m n : ℕ) (hm : m ≤ 2), h m n = n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (m n : ℕ)  :
    (m ≤ 2) ↔ (m < 4) := by
  omega

set_option maxHeartbeats 200000 in
example (m n : ℕ)  :
    (m ≤ 2) ↔ (m < 4) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (m n : ℕ)  :
    (m ≤ 2) ↔ (m < 4) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (m n : ℕ)  :
    (m ≤ 2) ↔ (m < 4) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (m n : ℕ)  :
    (m ≤ 2) ↔ (m < 4) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (m n : ℕ)  :
    (m ≤ 2) ↔ (m < 4) := by
  simp_all

set_option maxHeartbeats 200000 in
example (m n : ℕ)  :
    (m ≤ 2) ↔ (m < 4) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((m ≤ 2) ↔ (m < 4))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((m ≤ 2) ↔ (m < 4))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((m ≤ 2) ↔ (m < 4))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((m ≤ 2) ↔ (m < 4))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((m ≤ 2) ↔ (m < 4))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((m ≤ 2) ↔ (m < 4))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((m ≤ 2) ↔ (m < 4))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((m ≤ 2) ↔ (m < 4)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((m ≤ 2) ↔ (m < 4)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((m ≤ 2) ↔ (m < 4)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((m ≤ 2) ↔ (m < 4)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((m ≤ 2) ↔ (m < 4)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((m ≤ 2) ↔ (m < 4)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((m ≤ 2) ↔ (m < 4)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (m n : ℕ) (hm : m ≤ 2) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (m n : ℕ) (hm : m ≤ 2) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (m n : ℕ) (hm : m ≤ 2) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (m n : ℕ) (hm : m ≤ 2) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (m n : ℕ) (hm : m ≤ 2) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
