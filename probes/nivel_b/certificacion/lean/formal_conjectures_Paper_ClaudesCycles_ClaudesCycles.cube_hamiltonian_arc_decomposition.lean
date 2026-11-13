import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Claude's Cycles

*Reference:* [Claude's Cycles](https://www-cs-faculty.stanford.edu/~knuth/papers/claude-cycles.pdf)
by *Donald E. Knuth* (2026)

Fix `m ≥ 2`. Consider the directed graph with vertex set `(ZMod m)³`, where from each vertex
`(i, j, k)` there are directed arcs to `(i+1, j, k)`, `(i, j+1, k)`, and `(i, j, k+1)`
(arithmetic mod `m`). The goal is to partition all `3m³` directed arcs into three
edge-disjoint directed Hamiltonian cycles (each of length `m³`).

Knuth describes an explicit construction, found by Claude (Anthropic), that achieves this
decomposition for all odd `m ≥ 3`. The case `m = 2` is known to be impossible [Aub82].
The even case `m > 2` is also settled. Knuth's paper says so in its final section, added in the
14 April 2026 revision: "Breaking news: The problem for even values of m is no longer in doubt!"
Ho Boon Suan's algorithm [Ho26] is proved correct for even `m ≥ 8` in [GPT26], and
Aquino-Michaels [AM26] gives a decomposition for the even case that is simpler. The statement
below starts at `m = 4`, which is below the range [GPT26] covers, so it also rests on the
explicit solutions in [Kn26], whose header gives even `m ≥ 4`.

## References

- [Knu26] D. E. Knuth, "Claude's Cycles" (2026).
- [Aub82] J. Aubert, B. Schneider, "Graphes orientés indécomposables en circuits hamiltoniens",
  J. Combin. Theory Ser. B 32 (1982), 347–349.
- [Ho26] Ho Boon Suan, closed-form construction for even `m`,
  <https://cs.stanford.edu/~knuth/even_closed_form.c>
- [GPT26] A proof that [Ho26] yields three `m³`-cycles for every even `m ≥ 8`, 14 pages,
  <https://cs.stanford.edu/~knuth/even_closed_form_proof_final.pdf>
- [AM26] K. Aquino-Michaels, "Completing Claude's cycles: Multi-agent structured exploration on
  an open combinatorial problem", <https://github.com/no-way-labs/residue>
- [Kn26] Explicit even solutions for even `m ≥ 4`, recorded with [Knu26],
  <https://cs.stanford.edu/~knuth/even_solution.py>
- [KM26] K. Morrison, a Lean formalisation of the odd case,
  <https://github.com/kim-em/KnuthClaudeLean>
-/

section

namespace ClaudesCycles

/-- The vertex type: vectors in `(ZMod m)³`. -/
abbrev Vertex (m : ℕ) := Fin 3 → ZMod m

/-- Bump coordinate `b` of vertex `v`: add 1 to the `b`-th component. -/
def bumpAt {m : ℕ} [NeZero m] (b : Fin 3) (v : Vertex m) : Vertex m :=
  Function.update v b (v b + 1)

/-- Adjacency in the cube digraph: `u` is adjacent to `v` if `v` is obtained from `u` by
bumping one coordinate. -/
def cubeAdj {m : ℕ} [NeZero m] (u v : Vertex m) : Prop :=
  ∃ b : Fin 3, bumpAt b u = v

/-- A permutation `σ` on vertices is a directed Hamiltonian cycle of a digraph with adjacency
`adj` if every arc `(v, σ v)` is an edge, `σ` is a single cycle, and `σ` moves every vertex. -/
def IsDirectedHamiltonianCycle {V : Type*} [Fintype V] [DecidableEq V]
    (adj : V → V → Prop) (σ : Equiv.Perm V) : Prop :=
  (∀ v, adj v (σ v)) ∧ σ.IsCycle ∧ σ.support = Finset.univ

/-- The arcs of the cube digraph on `(ZMod m)³` can be decomposed into three directed
Hamiltonian cycles: there exist three permutations, each forming a directed Hamiltonian
cycle, such that every arc `(v, bumpAt b v)` belongs to exactly one cycle. -/
def HasHamiltonianArcDecomposition (m : ℕ) [NeZero m] : Prop :=
  ∃ σ : Fin 3 → Equiv.Perm (Vertex m),
    (∀ c, IsDirectedHamiltonianCycle (cubeAdj (m := m)) (σ c)) ∧
    (∀ v : Vertex m, ∀ b : Fin 3, ∃! c : Fin 3, σ c v = bumpAt b v)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m : ℕ} [NeZero m] (hm : Odd m), HasHamiltonianArcDecomposition m

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m), HasHamiltonianArcDecomposition m) →
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m), HasHamiltonianArcDecomposition m) →
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m), HasHamiltonianArcDecomposition m) →
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m), HasHamiltonianArcDecomposition m) →
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m), HasHamiltonianArcDecomposition m) →
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m), HasHamiltonianArcDecomposition m) →
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m), HasHamiltonianArcDecomposition m) →
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] (hm : Odd m) :
    (1 < m) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] (hm : Odd m) :
    (1 < m) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] (hm : Odd m) :
    (1 < m) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] (hm : Odd m) :
    (1 < m) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] (hm : Odd m) :
    (1 < m) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] (hm : Odd m) :
    (1 < m) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] (hm : Odd m) :
    (1 < m) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (Odd m) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (Odd m) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (Odd m) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (Odd m) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (Odd m) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (Odd m) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 ≤ m), HasHamiltonianArcDecomposition m

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 ≤ m), HasHamiltonianArcDecomposition m) →
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 ≤ m), HasHamiltonianArcDecomposition m) →
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 ≤ m), HasHamiltonianArcDecomposition m) →
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 ≤ m), HasHamiltonianArcDecomposition m) →
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 ≤ m), HasHamiltonianArcDecomposition m) →
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 ≤ m), HasHamiltonianArcDecomposition m) →
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 ≤ m), HasHamiltonianArcDecomposition m) →
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] (hm : Odd m) :
    (1 < m) ↔ (1 ≤ m) := by
  omega

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] (hm : Odd m) :
    (1 < m) ↔ (1 ≤ m) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] (hm : Odd m) :
    (1 < m) ↔ (1 ≤ m) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] (hm : Odd m) :
    (1 < m) ↔ (1 ≤ m) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] (hm : Odd m) :
    (1 < m) ↔ (1 ≤ m) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] (hm : Odd m) :
    (1 < m) ↔ (1 ≤ m) := by
  simp_all

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] (hm : Odd m) :
    (1 < m) ↔ (1 ≤ m) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (Odd m) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (Odd m) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (Odd m) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (Odd m) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (Odd m) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (Odd m) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (1 ≤ m)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (1 ≤ m)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (1 ≤ m)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (1 ≤ m)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (1 ≤ m)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (1 ≤ m)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : m > 1), HasHamiltonianArcDecomposition m

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] :
    (1 < m) ↔ (m > 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] :
    (1 < m) ↔ (m > 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] :
    (1 < m) ↔ (m > 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] :
    (1 < m) ↔ (m > 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] :
    (1 < m) ↔ (m > 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] :
    (1 < m) ↔ (m > 1) := by
  omega

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] :
    (1 < m) ↔ (m > 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] :
    (1 < m) ↔ (m > 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) ↔
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : m > 1), HasHamiltonianArcDecomposition m) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) ↔
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : m > 1), HasHamiltonianArcDecomposition m) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) ↔
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : m > 1), HasHamiltonianArcDecomposition m) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) ↔
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : m > 1), HasHamiltonianArcDecomposition m) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m : ℕ} [NeZero m] (hm' : 1 < m) (hm : Odd m), HasHamiltonianArcDecomposition m

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) ↔
    (∀ {m : ℕ} [NeZero m] (hm' : 1 < m) (hm : Odd m), HasHamiltonianArcDecomposition m) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) ↔
    (∀ {m : ℕ} [NeZero m] (hm' : 1 < m) (hm : Odd m), HasHamiltonianArcDecomposition m) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) ↔
    (∀ {m : ℕ} [NeZero m] (hm' : 1 < m) (hm : Odd m), HasHamiltonianArcDecomposition m) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) ↔
    (∀ {m : ℕ} [NeZero m] (hm' : 1 < m) (hm : Odd m), HasHamiltonianArcDecomposition m) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m : ℕ} [NeZero m] (hm₀ : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) ↔
    (∀ {m : ℕ} [NeZero m] (hm₀ : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) ↔
    (∀ {m : ℕ} [NeZero m] (hm₀ : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) ↔
    (∀ {m : ℕ} [NeZero m] (hm₀ : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) ↔
    (∀ {m : ℕ} [NeZero m] (hm₀ : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : ¬(m ≤ 1)), HasHamiltonianArcDecomposition m

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] :
    (1 < m) ↔ (¬(m ≤ 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] :
    (1 < m) ↔ (¬(m ≤ 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] :
    (1 < m) ↔ (¬(m ≤ 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] :
    (1 < m) ↔ (¬(m ≤ 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] :
    (1 < m) ↔ (¬(m ≤ 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] :
    (1 < m) ↔ (¬(m ≤ 1)) := by
  omega

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] :
    (1 < m) ↔ (¬(m ≤ 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] :
    (1 < m) ↔ (¬(m ≤ 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) ↔
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : ¬(m ≤ 1)), HasHamiltonianArcDecomposition m) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) ↔
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : ¬(m ≤ 1)), HasHamiltonianArcDecomposition m) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) ↔
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : ¬(m ≤ 1)), HasHamiltonianArcDecomposition m) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) ↔
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : ¬(m ≤ 1)), HasHamiltonianArcDecomposition m) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 2 ≤ m), HasHamiltonianArcDecomposition m

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] :
    (1 < m) ↔ (2 ≤ m) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] :
    (1 < m) ↔ (2 ≤ m) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] :
    (1 < m) ↔ (2 ≤ m) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] :
    (1 < m) ↔ (2 ≤ m) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] :
    (1 < m) ↔ (2 ≤ m) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] :
    (1 < m) ↔ (2 ≤ m) := by
  omega

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] :
    (1 < m) ↔ (2 ≤ m) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] :
    (1 < m) ↔ (2 ≤ m) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) ↔
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 2 ≤ m), HasHamiltonianArcDecomposition m) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) ↔
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 2 ≤ m), HasHamiltonianArcDecomposition m) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) ↔
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 2 ≤ m), HasHamiltonianArcDecomposition m) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) ↔
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 2 ≤ m), HasHamiltonianArcDecomposition m) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : m ≥ 1), HasHamiltonianArcDecomposition m

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : m ≥ 1), HasHamiltonianArcDecomposition m) →
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : m ≥ 1), HasHamiltonianArcDecomposition m) →
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : m ≥ 1), HasHamiltonianArcDecomposition m) →
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : m ≥ 1), HasHamiltonianArcDecomposition m) →
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : m ≥ 1), HasHamiltonianArcDecomposition m) →
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : m ≥ 1), HasHamiltonianArcDecomposition m) →
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : m ≥ 1), HasHamiltonianArcDecomposition m) →
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] (hm : Odd m) :
    (1 < m) ↔ (m ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] (hm : Odd m) :
    (1 < m) ↔ (m ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] (hm : Odd m) :
    (1 < m) ↔ (m ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] (hm : Odd m) :
    (1 < m) ↔ (m ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] (hm : Odd m) :
    (1 < m) ↔ (m ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] (hm : Odd m) :
    (1 < m) ↔ (m ≥ 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] (hm : Odd m) :
    (1 < m) ↔ (m ≥ 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (Odd m) ∧ (¬((1 < m) ↔ (m ≥ 1))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (Odd m) ∧ (¬((1 < m) ↔ (m ≥ 1))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (Odd m) ∧ (¬((1 < m) ↔ (m ≥ 1))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (Odd m) ∧ (¬((1 < m) ↔ (m ≥ 1))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (Odd m) ∧ (¬((1 < m) ↔ (m ≥ 1))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (Odd m) ∧ (¬((1 < m) ↔ (m ≥ 1))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (m ≥ 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (m ≥ 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (m ≥ 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (m ≥ 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (m ≥ 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (m ≥ 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 2 < m), HasHamiltonianArcDecomposition m

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) →
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 2 < m), HasHamiltonianArcDecomposition m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) →
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 2 < m), HasHamiltonianArcDecomposition m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) →
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 2 < m), HasHamiltonianArcDecomposition m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) →
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 2 < m), HasHamiltonianArcDecomposition m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) →
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 2 < m), HasHamiltonianArcDecomposition m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) →
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 2 < m), HasHamiltonianArcDecomposition m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m), HasHamiltonianArcDecomposition m) →
    (∀ {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 2 < m), HasHamiltonianArcDecomposition m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] (hm : Odd m) :
    (1 < m) ↔ (2 < m) := by
  omega

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] (hm : Odd m) :
    (1 < m) ↔ (2 < m) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] (hm : Odd m) :
    (1 < m) ↔ (2 < m) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] (hm : Odd m) :
    (1 < m) ↔ (2 < m) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] (hm : Odd m) :
    (1 < m) ↔ (2 < m) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] (hm : Odd m) :
    (1 < m) ↔ (2 < m) := by
  simp_all

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] (hm : Odd m) :
    (1 < m) ↔ (2 < m) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (Odd m) ∧ (¬((1 < m) ↔ (2 < m))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (Odd m) ∧ (¬((1 < m) ↔ (2 < m))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (Odd m) ∧ (¬((1 < m) ↔ (2 < m))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (Odd m) ∧ (¬((1 < m) ↔ (2 < m))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (Odd m) ∧ (¬((1 < m) ↔ (2 < m))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (Odd m) ∧ (¬((1 < m) ↔ (2 < m))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (2 < m)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (2 < m)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (2 < m)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (2 < m)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (2 < m)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (2 < m)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
