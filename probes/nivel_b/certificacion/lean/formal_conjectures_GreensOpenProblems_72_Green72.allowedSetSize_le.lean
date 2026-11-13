import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Ben Green's Open Problem 72

More commonly known as the **no-three-in-line problem**.

What is the largest subset of the grid $[N]^2$ with no three points in a line? In particular,
for $N$ sufficiently large, is it impossible to have a set of size $2N$ with this property?

The upper bound $2N$ is the easy half and is `allowedSetSize_le` below, by pigeonhole on the
columns. The open content is whether $2N$ is attained. Green records that it is for $N$ up to
around 50, that $(3/2 + o(1))N$ points are achievable for arbitrary $N$, and that his "personal
suspicion is that this is optimal". The Wikipedia reference points the same way: Guy and Kelly
conjectured $c = \sqrt[3]{2\pi^2/3} \approx 1.874$, and after an error in the heuristic was found
Guy corrected it to $c = \pi/\sqrt3 \approx 1.814$. Both are below $2$, so the expected answer to
the question above is yes.

*References:*
- [Ben Green's Open Problem 72](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.72)
- [Wikipedia](https://en.wikipedia.org/wiki/No-three-in-line_problem)
- [GK2025] Grebennikov, A. Kwan, M. No $(k + 1)$-in-line problem for large constant $k$.
  https://arxiv.org/abs/2510.17743
-/

section

namespace Green72

/-- We say a subset of $[N]^2$ is allowed for some $k$ if it contains no $k$ points
which lie on a common line. -/
structure AllowedSet (k : ℕ) (N : ℕ) (s : Finset (ℕ × ℕ)) : Prop where
  is_bounded : ∀ i ∈ s, i.1 < N ∧ i.2 < N
  not_collinear : ∀ ⦃t : Finset (ℕ × ℕ)⦄, t ⊆ s → t.card = k →
    ¬ Collinear ℝ ({r | ∃ i ∈ t, r = ((↑i.1 : ℝ), (↑i.2 : ℝ))} : Set (ℝ × ℝ))

/-- The maximal size of an allowed set -/
noncomputable def AllowedSetSize (k : ℕ) (N : ℕ) : ℕ :=
  sSup {r | ∃ s, r = s.card ∧ AllowedSet k N s}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N < (k - 1) * N

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N < (k - 1) * N) →
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N < (k - 1) * N) →
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N < (k - 1) * N) →
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N < (k - 1) * N) →
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N < (k - 1) * N) →
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N < (k - 1) * N) →
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N < (k - 1) * N) →
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N < (k - 1) * N)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≥ (k - 1) * N

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≥ (k - 1) * N) →
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≥ (k - 1) * N) →
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≥ (k - 1) * N) →
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≥ (k - 1) * N) →
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≥ (k - 1) * N) →
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≥ (k - 1) * N) →
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≥ (k - 1) * N) →
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) →
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≥ (k - 1) * N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) →
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≥ (k - 1) * N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) →
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≥ (k - 1) * N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) →
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≥ (k - 1) * N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) →
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≥ (k - 1) * N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) →
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≥ (k - 1) * N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) →
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≥ (k - 1) * N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬(AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ (AllowedSetSize k N ≥ (k - 1) * N)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k : ℕ} {N : ℕ}, (k - 1) * N ≥ AllowedSetSize k N

set_option maxHeartbeats 200000 in
example {k : ℕ} {N : ℕ} :
    (AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N ≥ AllowedSetSize k N) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {k : ℕ} {N : ℕ} :
    (AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N ≥ AllowedSetSize k N) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {k : ℕ} {N : ℕ} :
    (AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N ≥ AllowedSetSize k N) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {k : ℕ} {N : ℕ} :
    (AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N ≥ AllowedSetSize k N) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {k : ℕ} {N : ℕ} :
    (AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N ≥ AllowedSetSize k N) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {k : ℕ} {N : ℕ} :
    (AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N ≥ AllowedSetSize k N) := by
  omega

set_option maxHeartbeats 200000 in
example {k : ℕ} {N : ℕ} :
    (AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N ≥ AllowedSetSize k N) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {k : ℕ} {N : ℕ} :
    (AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N ≥ AllowedSetSize k N) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) ↔
    (∀ {k : ℕ} {N : ℕ}, (k - 1) * N ≥ AllowedSetSize k N) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) ↔
    (∀ {k : ℕ} {N : ℕ}, (k - 1) * N ≥ AllowedSetSize k N) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) ↔
    (∀ {k : ℕ} {N : ℕ}, (k - 1) * N ≥ AllowedSetSize k N) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) ↔
    (∀ {k : ℕ} {N : ℕ}, (k - 1) * N ≥ AllowedSetSize k N) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k : ℕ} {N : ℕ}, ¬((k - 1) * N < AllowedSetSize k N)

set_option maxHeartbeats 200000 in
example {k : ℕ} {N : ℕ} :
    (AllowedSetSize k N ≤ (k - 1) * N) ↔ (¬((k - 1) * N < AllowedSetSize k N)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {k : ℕ} {N : ℕ} :
    (AllowedSetSize k N ≤ (k - 1) * N) ↔ (¬((k - 1) * N < AllowedSetSize k N)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {k : ℕ} {N : ℕ} :
    (AllowedSetSize k N ≤ (k - 1) * N) ↔ (¬((k - 1) * N < AllowedSetSize k N)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {k : ℕ} {N : ℕ} :
    (AllowedSetSize k N ≤ (k - 1) * N) ↔ (¬((k - 1) * N < AllowedSetSize k N)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {k : ℕ} {N : ℕ} :
    (AllowedSetSize k N ≤ (k - 1) * N) ↔ (¬((k - 1) * N < AllowedSetSize k N)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {k : ℕ} {N : ℕ} :
    (AllowedSetSize k N ≤ (k - 1) * N) ↔ (¬((k - 1) * N < AllowedSetSize k N)) := by
  omega

set_option maxHeartbeats 200000 in
example {k : ℕ} {N : ℕ} :
    (AllowedSetSize k N ≤ (k - 1) * N) ↔ (¬((k - 1) * N < AllowedSetSize k N)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {k : ℕ} {N : ℕ} :
    (AllowedSetSize k N ≤ (k - 1) * N) ↔ (¬((k - 1) * N < AllowedSetSize k N)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) ↔
    (∀ {k : ℕ} {N : ℕ}, ¬((k - 1) * N < AllowedSetSize k N)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) ↔
    (∀ {k : ℕ} {N : ℕ}, ¬((k - 1) * N < AllowedSetSize k N)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) ↔
    (∀ {k : ℕ} {N : ℕ}, ¬((k - 1) * N < AllowedSetSize k N)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) ↔
    (∀ {k : ℕ} {N : ℕ}, ¬((k - 1) * N < AllowedSetSize k N)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k : ℕ} {N : ℕ}, (k - 1) * N > AllowedSetSize k N

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, (k - 1) * N > AllowedSetSize k N) →
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, (k - 1) * N > AllowedSetSize k N) →
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, (k - 1) * N > AllowedSetSize k N) →
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, (k - 1) * N > AllowedSetSize k N) →
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, (k - 1) * N > AllowedSetSize k N) →
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, (k - 1) * N > AllowedSetSize k N) →
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, (k - 1) * N > AllowedSetSize k N) →
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N > AllowedSetSize k N)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k : ℕ} {N : ℕ}, (k - 1) * N ≤ AllowedSetSize k N

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, (k - 1) * N ≤ AllowedSetSize k N) →
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, (k - 1) * N ≤ AllowedSetSize k N) →
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, (k - 1) * N ≤ AllowedSetSize k N) →
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, (k - 1) * N ≤ AllowedSetSize k N) →
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, (k - 1) * N ≤ AllowedSetSize k N) →
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, (k - 1) * N ≤ AllowedSetSize k N) →
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, (k - 1) * N ≤ AllowedSetSize k N) →
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) →
    (∀ {k : ℕ} {N : ℕ}, (k - 1) * N ≤ AllowedSetSize k N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) →
    (∀ {k : ℕ} {N : ℕ}, (k - 1) * N ≤ AllowedSetSize k N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) →
    (∀ {k : ℕ} {N : ℕ}, (k - 1) * N ≤ AllowedSetSize k N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) →
    (∀ {k : ℕ} {N : ℕ}, (k - 1) * N ≤ AllowedSetSize k N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) →
    (∀ {k : ℕ} {N : ℕ}, (k - 1) * N ≤ AllowedSetSize k N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) →
    (∀ {k : ℕ} {N : ℕ}, (k - 1) * N ≤ AllowedSetSize k N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k : ℕ} {N : ℕ}, AllowedSetSize k N ≤ (k - 1) * N) →
    (∀ {k : ℕ} {N : ℕ}, (k - 1) * N ≤ AllowedSetSize k N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), (¬((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (N : ℕ), ¬((AllowedSetSize k N ≤ (k - 1) * N) ↔ ((k - 1) * N ≤ AllowedSetSize k N)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

#eval "FIN_CERTIFICAR"
