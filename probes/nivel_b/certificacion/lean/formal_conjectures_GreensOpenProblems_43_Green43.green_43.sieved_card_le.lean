import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Ben Green's Open Problem 43

*References:*
- [Gr24] [Ben Green's Open Problem 43](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.43)
- [Gr18] Green, Ben. "A note on multiplicative functions on progressions to large moduli."
  Proc. Roy. Soc. Edinburgh Sect. A 148 (2018), no. 1, 63–77. (Problem 43 is formulated here,
  [Gr18, Section 4].)
- [AP92] Alon, Noga, and Yuval Peres. "Uniform dilations." Geometric and Functional Analysis
  2 (1992), no. 1, 1–28. (Source of the favourite variant in [Gr24, Comments to Problem 43].)
-/

section

open Filter Topology

namespace Green43

open Classical in
/-- The *sieved subset* of `[1, N]`: those `n ∈ [1, N]` with `n ≡ a p (mod p)` for some prime
`p` in the range `lo ≤ p < hi`. This is the set counted in `green_43`. -/
noncomputable def sievedSet (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) : Finset ℤ :=
  (Finset.Icc (1 : ℤ) (N : ℤ)).filter fun n => ∃ p, Nat.Prime p ∧
  lo ≤ (p : ℝ) ∧ (p : ℝ) < hi ∧ (p : ℤ) ∣ ((n : ℤ) - a p)

/-- The size of the sieved subset `sievedSet N a lo hi`. -/
noncomputable def sievedCard (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) : ℕ :=
  (sievedSet N a lo hi).card

/--
[Gr24, Comments to Problem 43] The statement that the lower bound `N^{1-o(1)}` holds for the
sieved set, where for each `N` the sieving primes range over `[lo N, hi N)`. Problem 43 is the
case `lo N = N^{0.51}`, `hi N = 2 N^{0.51}`; the minor variants only change this range.
-/
def SievedLowerBound (lo hi : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ a : ℕ → ℤ, (N : ℝ) ^ (1 - ε) ≤ sievedCard N a (lo N) (hi N)

/-- The exponent-`α` instance of Problem 43: the `N^{1-o(1)}` lower bound for sieving primes in
`[N^α, 2 N^α)`. Problem 43 is `SievedLowerBoundExp 0.51`. -/
def SievedLowerBoundExp (α : ℝ) : Prop :=
  SievedLowerBound (fun N => (N : ℝ) ^ α) (fun N => 2 * (N : ℝ) ^ α)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi < N

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi < N) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi < N) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi < N) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi < N) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi < N) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi < N) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi < N) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≥ N

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≥ N) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≥ N) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≥ N) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≥ N) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≥ N) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≥ N) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≥ N) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≥ N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≥ N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≥ N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≥ N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≥ N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≥ N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≥ N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), N ≥ sievedCard N a lo hi

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) :
    (sievedCard N a lo hi ≤ N) ↔ (N ≥ sievedCard N a lo hi) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) :
    (sievedCard N a lo hi ≤ N) ↔ (N ≥ sievedCard N a lo hi) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) :
    (sievedCard N a lo hi ≤ N) ↔ (N ≥ sievedCard N a lo hi) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) :
    (sievedCard N a lo hi ≤ N) ↔ (N ≥ sievedCard N a lo hi) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) :
    (sievedCard N a lo hi ≤ N) ↔ (N ≥ sievedCard N a lo hi) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) :
    (sievedCard N a lo hi ≤ N) ↔ (N ≥ sievedCard N a lo hi) := by
  omega

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) :
    (sievedCard N a lo hi ≤ N) ↔ (N ≥ sievedCard N a lo hi) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) :
    (sievedCard N a lo hi ≤ N) ↔ (N ≥ sievedCard N a lo hi) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N) ↔
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), N ≥ sievedCard N a lo hi) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N) ↔
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), N ≥ sievedCard N a lo hi) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N) ↔
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), N ≥ sievedCard N a lo hi) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N) ↔
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), N ≥ sievedCard N a lo hi) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), N > sievedCard N a lo hi

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), N > sievedCard N a lo hi) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), N > sievedCard N a lo hi) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), N > sievedCard N a lo hi) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), N > sievedCard N a lo hi) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), N > sievedCard N a lo hi) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), N > sievedCard N a lo hi) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), N > sievedCard N a lo hi) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), N ≤ sievedCard N a lo hi

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), N ≤ sievedCard N a lo hi) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), N ≤ sievedCard N a lo hi) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), N ≤ sievedCard N a lo hi) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), N ≤ sievedCard N a lo hi) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), N ≤ sievedCard N a lo hi) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), N ≤ sievedCard N a lo hi) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), N ≤ sievedCard N a lo hi) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), N ≤ sievedCard N a lo hi) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), N ≤ sievedCard N a lo hi) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), N ≤ sievedCard N a lo hi) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), N ≤ sievedCard N a lo hi) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), N ≤ sievedCard N a lo hi) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), N ≤ sievedCard N a lo hi) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), sievedCard N a lo hi ≤ N) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ), N ≤ sievedCard N a lo hi) := by
  intro h; intros; aesop

#eval "FIN_CERTIFICAR"
