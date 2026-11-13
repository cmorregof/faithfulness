import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 667

A problem of Erdős, Faudree, Rousseau, and Schelp on the growth exponent of the largest clique
that is guaranteed inside a locally dense graph.

*References:*
* [erdosproblems.com/667](https://www.erdosproblems.com/667)
* [Er97f] P. Erdős, _Some unsolved problems_. In: Combinatorics, Geometry and Probability
  (Cambridge, 1993), Cambridge Univ. Press (1997), 1-10.
* [EFRS94] P. Erdős, R. J. Faudree, C. C. Rousseau and R. H. Schelp,
  _A local density condition for triangles_. Discrete Math. 127 (1994), 153-161.
-/

section
open SimpleGraph Filter

namespace Erdos667

/-- A graph `G` on `n` vertices is *`(p, q)`-locally dense* if every set of `p` of its vertices
spans at least `q` edges of `G`; equivalently, every induced subgraph on `p` vertices has at
least `q` edges. -/
def LocallyDense (p q : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ s : Finset (Fin n), s.card = p → q ≤ (G.induce s).edgeSet.ncard

open Classical in
/-- `H p q n` is `H(n) = H(n; p, q)`: the largest `m` such that *every* `(p, q)`-locally dense
graph on `n` vertices must contain a complete graph on `m` vertices `Kₘ`.

The condition "`G` contains `Kₘ`" is `¬ G.CliqueFree m`. Any `m`-clique needs `m ≤ n` vertices,
and the property is downward closed in `m`, so `Nat.findGreatest _ n` returns the genuine maximum. -/
noncomputable def H (p q n : ℕ) : ℕ :=
  Nat.findGreatest
    (fun m => ∀ G : SimpleGraph (Fin n), LocallyDense p q G → ¬ G.CliqueFree m) n

/-- The growth exponent `c(p, q) = liminf_{n → ∞} (log H(n)) / (log n)`. -/
noncomputable def c (p q : ℕ) : ℝ :=
  liminf (fun n : ℕ => Real.log (H p q n) / Real.log n) atTop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : 3 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) →
    (∀ (p : ℕ) (hp : 3 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) →
    (∀ (p : ℕ) (hp : 3 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) →
    (∀ (p : ℕ) (hp : 3 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) →
    (∀ (p : ℕ) (hp : 3 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) →
    (∀ (p : ℕ) (hp : 3 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) →
    (∀ (p : ℕ) (hp : 3 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) →
    (∀ (p : ℕ) (hp : 3 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p : ℕ)  :
    (2 ≤ p) ↔ (3 ≤ p) := by
  omega

set_option maxHeartbeats 200000 in
example (p : ℕ)  :
    (2 ≤ p) ↔ (3 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p : ℕ)  :
    (2 ≤ p) ↔ (3 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p : ℕ)  :
    (2 ≤ p) ↔ (3 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p : ℕ)  :
    (2 ≤ p) ↔ (3 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p : ℕ)  :
    (2 ≤ p) ↔ (3 ≤ p) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p : ℕ)  :
    (2 ≤ p) ↔ (3 ≤ p) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (¬((2 ≤ p) ↔ (3 ≤ p))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (¬((2 ≤ p) ↔ (3 ≤ p))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (¬((2 ≤ p) ↔ (3 ≤ p))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (¬((2 ≤ p) ↔ (3 ≤ p))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (¬((2 ≤ p) ↔ (3 ≤ p))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (¬((2 ≤ p) ↔ (3 ≤ p))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (¬((2 ≤ p) ↔ (3 ≤ p))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((2 ≤ p) ↔ (3 ≤ p)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((2 ≤ p) ↔ (3 ≤ p)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((2 ≤ p) ↔ (3 ≤ p)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((2 ≤ p) ↔ (3 ≤ p)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((2 ≤ p) ↔ (3 ≤ p)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((2 ≤ p) ↔ (3 ≤ p)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((2 ≤ p) ↔ (3 ≤ p)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : p ≥ 2), c p (Nat.choose (p - 1) 2 + 1) = 1

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (2 ≤ p) ↔ (p ≥ 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (2 ≤ p) ↔ (p ≥ 2) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (2 ≤ p) ↔ (p ≥ 2) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (2 ≤ p) ↔ (p ≥ 2) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (2 ≤ p) ↔ (p ≥ 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (2 ≤ p) ↔ (p ≥ 2) := by
  omega

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (2 ≤ p) ↔ (p ≥ 2) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (2 ≤ p) ↔ (p ≥ 2) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) ↔
    (∀ (p : ℕ) (hp : p ≥ 2), c p (Nat.choose (p - 1) 2 + 1) = 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) ↔
    (∀ (p : ℕ) (hp : p ≥ 2), c p (Nat.choose (p - 1) 2 + 1) = 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) ↔
    (∀ (p : ℕ) (hp : p ≥ 2), c p (Nat.choose (p - 1) 2 + 1) = 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) ↔
    (∀ (p : ℕ) (hp : p ≥ 2), c p (Nat.choose (p - 1) 2 + 1) = 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp₀ : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) ↔
    (∀ (p : ℕ) (hp₀ : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) ↔
    (∀ (p : ℕ) (hp₀ : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) ↔
    (∀ (p : ℕ) (hp₀ : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) ↔
    (∀ (p : ℕ) (hp₀ : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : ¬(p < 2)), c p (Nat.choose (p - 1) 2 + 1) = 1

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (2 ≤ p) ↔ (¬(p < 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (2 ≤ p) ↔ (¬(p < 2)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (2 ≤ p) ↔ (¬(p < 2)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (2 ≤ p) ↔ (¬(p < 2)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (2 ≤ p) ↔ (¬(p < 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (2 ≤ p) ↔ (¬(p < 2)) := by
  omega

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (2 ≤ p) ↔ (¬(p < 2)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (2 ≤ p) ↔ (¬(p < 2)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) ↔
    (∀ (p : ℕ) (hp : ¬(p < 2)), c p (Nat.choose (p - 1) 2 + 1) = 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) ↔
    (∀ (p : ℕ) (hp : ¬(p < 2)), c p (Nat.choose (p - 1) 2 + 1) = 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) ↔
    (∀ (p : ℕ) (hp : ¬(p < 2)), c p (Nat.choose (p - 1) 2 + 1) = 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) ↔
    (∀ (p : ℕ) (hp : ¬(p < 2)), c p (Nat.choose (p - 1) 2 + 1) = 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : 1 < p), c p (Nat.choose (p - 1) 2 + 1) = 1

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (2 ≤ p) ↔ (1 < p) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (2 ≤ p) ↔ (1 < p) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (2 ≤ p) ↔ (1 < p) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (2 ≤ p) ↔ (1 < p) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (2 ≤ p) ↔ (1 < p) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (2 ≤ p) ↔ (1 < p) := by
  omega

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (2 ≤ p) ↔ (1 < p) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (2 ≤ p) ↔ (1 < p) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) ↔
    (∀ (p : ℕ) (hp : 1 < p), c p (Nat.choose (p - 1) 2 + 1) = 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) ↔
    (∀ (p : ℕ) (hp : 1 < p), c p (Nat.choose (p - 1) 2 + 1) = 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) ↔
    (∀ (p : ℕ) (hp : 1 < p), c p (Nat.choose (p - 1) 2 + 1) = 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) ↔
    (∀ (p : ℕ) (hp : 1 < p), c p (Nat.choose (p - 1) 2 + 1) = 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : p ≥ 3), c p (Nat.choose (p - 1) 2 + 1) = 1

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) →
    (∀ (p : ℕ) (hp : p ≥ 3), c p (Nat.choose (p - 1) 2 + 1) = 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) →
    (∀ (p : ℕ) (hp : p ≥ 3), c p (Nat.choose (p - 1) 2 + 1) = 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) →
    (∀ (p : ℕ) (hp : p ≥ 3), c p (Nat.choose (p - 1) 2 + 1) = 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) →
    (∀ (p : ℕ) (hp : p ≥ 3), c p (Nat.choose (p - 1) 2 + 1) = 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) →
    (∀ (p : ℕ) (hp : p ≥ 3), c p (Nat.choose (p - 1) 2 + 1) = 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) →
    (∀ (p : ℕ) (hp : p ≥ 3), c p (Nat.choose (p - 1) 2 + 1) = 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) →
    (∀ (p : ℕ) (hp : p ≥ 3), c p (Nat.choose (p - 1) 2 + 1) = 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p : ℕ)  :
    (2 ≤ p) ↔ (p ≥ 3) := by
  omega

set_option maxHeartbeats 200000 in
example (p : ℕ)  :
    (2 ≤ p) ↔ (p ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p : ℕ)  :
    (2 ≤ p) ↔ (p ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p : ℕ)  :
    (2 ≤ p) ↔ (p ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p : ℕ)  :
    (2 ≤ p) ↔ (p ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p : ℕ)  :
    (2 ≤ p) ↔ (p ≥ 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p : ℕ)  :
    (2 ≤ p) ↔ (p ≥ 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (¬((2 ≤ p) ↔ (p ≥ 3))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (¬((2 ≤ p) ↔ (p ≥ 3))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (¬((2 ≤ p) ↔ (p ≥ 3))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (¬((2 ≤ p) ↔ (p ≥ 3))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (¬((2 ≤ p) ↔ (p ≥ 3))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (¬((2 ≤ p) ↔ (p ≥ 3))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (¬((2 ≤ p) ↔ (p ≥ 3))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((2 ≤ p) ↔ (p ≥ 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((2 ≤ p) ↔ (p ≥ 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((2 ≤ p) ↔ (p ≥ 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((2 ≤ p) ↔ (p ≥ 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((2 ≤ p) ↔ (p ≥ 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((2 ≤ p) ↔ (p ≥ 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((2 ≤ p) ↔ (p ≥ 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : 1 < p), c p (Nat.choose (p - 1) 3 + 1) = 1

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : 1 < p), c p (Nat.choose (p - 1) 3 + 1) = 1) →
    (∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : 1 < p), c p (Nat.choose (p - 1) 3 + 1) = 1) →
    (∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : 1 < p), c p (Nat.choose (p - 1) 3 + 1) = 1) →
    (∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : 1 < p), c p (Nat.choose (p - 1) 3 + 1) = 1) →
    (∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : 1 < p), c p (Nat.choose (p - 1) 3 + 1) = 1) →
    (∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : 1 < p), c p (Nat.choose (p - 1) 3 + 1) = 1) →
    (∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : 1 < p), c p (Nat.choose (p - 1) 3 + 1) = 1) →
    (∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) →
    (∀ (p : ℕ) (hp : 1 < p), c p (Nat.choose (p - 1) 3 + 1) = 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) →
    (∀ (p : ℕ) (hp : 1 < p), c p (Nat.choose (p - 1) 3 + 1) = 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) →
    (∀ (p : ℕ) (hp : 1 < p), c p (Nat.choose (p - 1) 3 + 1) = 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) →
    (∀ (p : ℕ) (hp : 1 < p), c p (Nat.choose (p - 1) 3 + 1) = 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) →
    (∀ (p : ℕ) (hp : 1 < p), c p (Nat.choose (p - 1) 3 + 1) = 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) →
    (∀ (p : ℕ) (hp : 1 < p), c p (Nat.choose (p - 1) 3 + 1) = 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : 2 ≤ p), c p (Nat.choose (p - 1) 2 + 1) = 1) →
    (∀ (p : ℕ) (hp : 1 < p), c p (Nat.choose (p - 1) 3 + 1) = 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (2 ≤ p) ∧ (¬(c p (Nat.choose (p - 1) 3 + 1) = 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (2 ≤ p) ∧ (¬(c p (Nat.choose (p - 1) 3 + 1) = 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (2 ≤ p) ∧ (¬(c p (Nat.choose (p - 1) 3 + 1) = 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (2 ≤ p) ∧ (¬(c p (Nat.choose (p - 1) 3 + 1) = 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (2 ≤ p) ∧ (¬(c p (Nat.choose (p - 1) 3 + 1) = 1)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (2 ≤ p) ∧ (¬(c p (Nat.choose (p - 1) 3 + 1) = 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (2 ≤ p) ∧ (¬(c p (Nat.choose (p - 1) 3 + 1) = 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((c p (Nat.choose (p - 1) 2 + 1) = 1) ↔ (c p (Nat.choose (p - 1) 3 + 1) = 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((c p (Nat.choose (p - 1) 2 + 1) = 1) ↔ (c p (Nat.choose (p - 1) 3 + 1) = 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((c p (Nat.choose (p - 1) 2 + 1) = 1) ↔ (c p (Nat.choose (p - 1) 3 + 1) = 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((c p (Nat.choose (p - 1) 2 + 1) = 1) ↔ (c p (Nat.choose (p - 1) 3 + 1) = 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((c p (Nat.choose (p - 1) 2 + 1) = 1) ↔ (c p (Nat.choose (p - 1) 3 + 1) = 1)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((c p (Nat.choose (p - 1) 2 + 1) = 1) ↔ (c p (Nat.choose (p - 1) 3 + 1) = 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((c p (Nat.choose (p - 1) 2 + 1) = 1) ↔ (c p (Nat.choose (p - 1) 3 + 1) = 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : 2 ≤ p) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : 2 ≤ p) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : 2 ≤ p) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : 2 ≤ p) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : 2 ≤ p) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
