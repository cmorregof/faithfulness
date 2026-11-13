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
  ∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi) :
    ((p : ℤ) ≤ (N : ℤ)) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi) :
    ((p : ℤ) ≤ (N : ℤ)) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi) :
    ((p : ℤ) ≤ (N : ℤ)) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi) :
    ((p : ℤ) ≤ (N : ℤ)) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi) :
    ((p : ℤ) ≤ (N : ℤ)) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi) :
    ((p : ℤ) ≤ (N : ℤ)) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi) :
    ((p : ℤ) ≤ (N : ℤ)) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℝ), (0 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℝ), (1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℝ), (0 : ℝ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℝ), (1 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℝ), (-1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℝ), (0 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℝ), (1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(0 : ℕ), (-1 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℝ), (0 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℝ), (1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℝ), (1 : ℝ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℝ), (-1 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℝ), (0 : ℝ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℝ), (1 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℝ), (-1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(0 : ℕ), (-1 : ℝ), (0 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(0 : ℕ), (-1 : ℝ), (1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℝ), (0 : ℝ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℝ), (1 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℝ), (-1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℝ), (0 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℝ), (1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(1 : ℕ), (-1 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℝ), (0 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℝ), (1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℝ), (-1 : ℝ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) ≤ hi), (sievedSet N a lo hi).Nonempty

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) ≤ hi), (sievedSet N a lo hi).Nonempty) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) ≤ hi), (sievedSet N a lo hi).Nonempty) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) ≤ hi), (sievedSet N a lo hi).Nonempty) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) ≤ hi), (sievedSet N a lo hi).Nonempty) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) ≤ hi), (sievedSet N a lo hi).Nonempty) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) ≤ hi), (sievedSet N a lo hi).Nonempty) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) ≤ hi), (sievedSet N a lo hi).Nonempty) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) :
    ((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi) := by
  omega

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) :
    ((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) :
    ((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) :
    ((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) :
    ((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) :
    ((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi) := by
  simp_all

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) :
    ((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(0 : ℕ), (0 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(0 : ℕ), (0 : ℝ), (0 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(0 : ℕ), (0 : ℝ), (1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(0 : ℕ), (1 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(1 : ℕ), (0 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(0 : ℕ), (0 : ℝ), (0 : ℝ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(0 : ℕ), (0 : ℝ), (1 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(0 : ℕ), (0 : ℝ), (-1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(0 : ℕ), (1 : ℝ), (0 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(0 : ℕ), (1 : ℝ), (1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(0 : ℕ), (-1 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(1 : ℕ), (0 : ℝ), (0 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(1 : ℕ), (0 : ℝ), (1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(1 : ℕ), (1 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(2 : ℕ), (0 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(0 : ℕ), (0 : ℝ), (1 : ℝ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(0 : ℕ), (0 : ℝ), (-1 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(0 : ℕ), (1 : ℝ), (0 : ℝ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(0 : ℕ), (1 : ℝ), (1 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(0 : ℕ), (1 : ℝ), (-1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(0 : ℕ), (-1 : ℝ), (0 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(0 : ℕ), (-1 : ℝ), (1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(1 : ℕ), (0 : ℝ), (0 : ℝ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(1 : ℕ), (0 : ℝ), (1 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(1 : ℕ), (0 : ℝ), (-1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(1 : ℕ), (1 : ℝ), (0 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(1 : ℕ), (1 : ℝ), (1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(1 : ℕ), (-1 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(2 : ℕ), (0 : ℝ), (0 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(2 : ℕ), (0 : ℝ), (1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(2 : ℕ), (1 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(0 : ℕ), (0 : ℝ), (-1 : ℝ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(0 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(0 : ℝ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(1 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(-1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(0 : ℝ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(1 : ℝ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(-1 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(2 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(0 : ℝ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(1 : ℝ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(-1 : ℝ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(2 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(1/2 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(0 : ℝ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(1 : ℝ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(-1 : ℝ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(2 : ℝ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(1/2 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(3 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(1 : ℝ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(-1 : ℝ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(2 : ℝ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(1/2 : ℝ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(3 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(-1 : ℝ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(2 : ℝ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(1/2 : ℝ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(3 : ℝ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(2 : ℝ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(1/2 : ℝ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) < (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) < (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) < (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) < (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) < (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) < (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) < (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) < (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi) :
    ((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ)) := by
  omega

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi) :
    ((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ)) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi) :
    ((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ)) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi) :
    ((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ)) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi) :
    ((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ)) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi) :
    ((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ)) := by
  simp_all

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi) :
    ((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ)) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ)))) :=
  ⟨(0 : ℕ), (0 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ)))) :=
  ⟨(0 : ℕ), (0 : ℝ), (0 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ)))) :=
  ⟨(0 : ℕ), (0 : ℝ), (1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ)))) :=
  ⟨(0 : ℕ), (1 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ)))) :=
  ⟨(1 : ℕ), (0 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ)))) :=
  ⟨(0 : ℕ), (0 : ℝ), (0 : ℝ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ)))) :=
  ⟨(0 : ℕ), (0 : ℝ), (1 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ)))) :=
  ⟨(0 : ℕ), (0 : ℝ), (-1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ)))) :=
  ⟨(0 : ℕ), (1 : ℝ), (0 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ)))) :=
  ⟨(0 : ℕ), (1 : ℝ), (1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ)))) :=
  ⟨(0 : ℕ), (-1 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ)))) :=
  ⟨(1 : ℕ), (0 : ℝ), (0 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ)))) :=
  ⟨(1 : ℕ), (0 : ℝ), (1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ)))) :=
  ⟨(1 : ℕ), (1 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ)))) :=
  ⟨(2 : ℕ), (0 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ)))) :=
  ⟨(0 : ℕ), (0 : ℝ), (1 : ℝ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ)))) :=
  ⟨(0 : ℕ), (0 : ℝ), (-1 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ)))) :=
  ⟨(0 : ℕ), (1 : ℝ), (0 : ℝ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ)))) :=
  ⟨(0 : ℕ), (1 : ℝ), (1 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ)))) :=
  ⟨(0 : ℕ), (1 : ℝ), (-1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ)))) :=
  ⟨(0 : ℕ), (-1 : ℝ), (0 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ)))) :=
  ⟨(0 : ℕ), (-1 : ℝ), (1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ)))) :=
  ⟨(1 : ℕ), (0 : ℝ), (0 : ℝ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ)))) :=
  ⟨(1 : ℕ), (0 : ℝ), (1 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ)))) :=
  ⟨(1 : ℕ), (0 : ℝ), (-1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ)))) :=
  ⟨(1 : ℕ), (1 : ℝ), (0 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ)))) :=
  ⟨(1 : ℕ), (1 : ℝ), (1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ)))) :=
  ⟨(1 : ℕ), (-1 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ)))) :=
  ⟨(2 : ℕ), (0 : ℝ), (0 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ)))) :=
  ⟨(2 : ℕ), (0 : ℝ), (1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ)))) :=
  ⟨(2 : ℕ), (1 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ)))) :=
  ⟨(0 : ℕ), (0 : ℝ), (-1 : ℝ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((p : ℤ) < (N : ℤ))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (N : ℤ) ≥ (p : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) :
    ((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) ≥ (p : ℤ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) :
    ((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) ≥ (p : ℤ)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) :
    ((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) ≥ (p : ℤ)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) :
    ((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) ≥ (p : ℤ)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) :
    ((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) ≥ (p : ℤ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) :
    ((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) ≥ (p : ℤ)) := by
  omega

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) :
    ((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) ≥ (p : ℤ)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) :
    ((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) ≥ (p : ℤ)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) ↔
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (N : ℤ) ≥ (p : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) ↔
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (N : ℤ) ≥ (p : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) ↔
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (N : ℤ) ≥ (p : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) ↔
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (N : ℤ) ≥ (p : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hpN : (p : ℤ) ≤ (N : ℤ)) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) ↔
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hpN : (p : ℤ) ≤ (N : ℤ)) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) ↔
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hpN : (p : ℤ) ≤ (N : ℤ)) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) ↔
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hpN : (p : ℤ) ≤ (N : ℤ)) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) ↔
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hpN : (p : ℤ) ≤ (N : ℤ)) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp₀ : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) ↔
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp₀ : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) ↔
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp₀ : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) ↔
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp₀ : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) ↔
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp₀ : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : ¬((N : ℤ) < (p : ℤ))) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) :
    ((p : ℤ) ≤ (N : ℤ)) ↔ (¬((N : ℤ) < (p : ℤ))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) :
    ((p : ℤ) ≤ (N : ℤ)) ↔ (¬((N : ℤ) < (p : ℤ))) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) :
    ((p : ℤ) ≤ (N : ℤ)) ↔ (¬((N : ℤ) < (p : ℤ))) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) :
    ((p : ℤ) ≤ (N : ℤ)) ↔ (¬((N : ℤ) < (p : ℤ))) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) :
    ((p : ℤ) ≤ (N : ℤ)) ↔ (¬((N : ℤ) < (p : ℤ))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) :
    ((p : ℤ) ≤ (N : ℤ)) ↔ (¬((N : ℤ) < (p : ℤ))) := by
  omega

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) :
    ((p : ℤ) ≤ (N : ℤ)) ↔ (¬((N : ℤ) < (p : ℤ))) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) :
    ((p : ℤ) ≤ (N : ℤ)) ↔ (¬((N : ℤ) < (p : ℤ))) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) ↔
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : ¬((N : ℤ) < (p : ℤ))) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) ↔
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : ¬((N : ℤ) < (p : ℤ))) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) ↔
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : ¬((N : ℤ) < (p : ℤ))) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) ↔
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : ¬((N : ℤ) < (p : ℤ))) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (N : ℤ) ≥ (p : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) ≤ hi), (sievedSet N a lo hi).Nonempty

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (N : ℤ) ≥ (p : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) ≤ hi), (sievedSet N a lo hi).Nonempty) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (N : ℤ) ≥ (p : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) ≤ hi), (sievedSet N a lo hi).Nonempty) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (N : ℤ) ≥ (p : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) ≤ hi), (sievedSet N a lo hi).Nonempty) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (N : ℤ) ≥ (p : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) ≤ hi), (sievedSet N a lo hi).Nonempty) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (N : ℤ) ≥ (p : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) ≤ hi), (sievedSet N a lo hi).Nonempty) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (N : ℤ) ≥ (p : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) ≤ hi), (sievedSet N a lo hi).Nonempty) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (N : ℤ) ≥ (p : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) ≤ hi), (sievedSet N a lo hi).Nonempty) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) :
    ((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi) := by
  omega

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) :
    ((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) :
    ((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) :
    ((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) :
    ((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) :
    ((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi) := by
  simp_all

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) :
    ((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(0 : ℕ), (0 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(0 : ℕ), (0 : ℝ), (0 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(0 : ℕ), (0 : ℝ), (1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(0 : ℕ), (1 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(1 : ℕ), (0 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(0 : ℕ), (0 : ℝ), (0 : ℝ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(0 : ℕ), (0 : ℝ), (1 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(0 : ℕ), (0 : ℝ), (-1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(0 : ℕ), (1 : ℝ), (0 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(0 : ℕ), (1 : ℝ), (1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(0 : ℕ), (-1 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(1 : ℕ), (0 : ℝ), (0 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(1 : ℕ), (0 : ℝ), (1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(1 : ℕ), (1 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(2 : ℕ), (0 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(0 : ℕ), (0 : ℝ), (1 : ℝ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(0 : ℕ), (0 : ℝ), (-1 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(0 : ℕ), (1 : ℝ), (0 : ℝ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(0 : ℕ), (1 : ℝ), (1 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(0 : ℕ), (1 : ℝ), (-1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(0 : ℕ), (-1 : ℝ), (0 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(0 : ℕ), (-1 : ℝ), (1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(1 : ℕ), (0 : ℝ), (0 : ℝ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(1 : ℕ), (0 : ℝ), (1 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(1 : ℕ), (0 : ℝ), (-1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(1 : ℕ), (1 : ℝ), (0 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(1 : ℕ), (1 : ℝ), (1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(1 : ℕ), (-1 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(2 : ℕ), (0 : ℝ), (0 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(2 : ℕ), (0 : ℝ), (1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(2 : ℕ), (1 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ ((p : ℤ) ≤ (N : ℤ)) ∧ (lo ≤ (p : ℝ)) ∧ (¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi))) :=
  ⟨(0 : ℕ), (0 : ℝ), (-1 : ℝ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(0 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(0 : ℝ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(1 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(-1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(0 : ℝ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(1 : ℝ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(-1 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(2 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(0 : ℝ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(1 : ℝ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(-1 : ℝ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(2 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(1/2 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(0 : ℝ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(1 : ℝ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(-1 : ℝ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(2 : ℝ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(1/2 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(3 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(1 : ℝ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(-1 : ℝ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(2 : ℝ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(1/2 : ℝ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(3 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(-1 : ℝ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(2 : ℝ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(1/2 : ℝ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(3 : ℝ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(2 : ℝ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (hi : ℝ) (p : ℕ), ¬(((p : ℝ) < hi) ↔ ((p : ℝ) ≤ hi)) :=
  ⟨(1/2 : ℝ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (N : ℤ) > (p : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (N : ℤ) > (p : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (N : ℤ) > (p : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (N : ℤ) > (p : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (N : ℤ) > (p : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (N : ℤ) > (p : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (N : ℤ) > (p : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (N : ℤ) > (p : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi) :
    ((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ)) := by
  omega

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi) :
    ((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ)) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi) :
    ((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ)) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi) :
    ((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ)) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi) :
    ((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ)) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi) :
    ((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ)) := by
  simp_all

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi) :
    ((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ)) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ)))) :=
  ⟨(0 : ℕ), (0 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ)))) :=
  ⟨(0 : ℕ), (0 : ℝ), (0 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ)))) :=
  ⟨(0 : ℕ), (0 : ℝ), (1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ)))) :=
  ⟨(0 : ℕ), (1 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ)))) :=
  ⟨(1 : ℕ), (0 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ)))) :=
  ⟨(0 : ℕ), (0 : ℝ), (0 : ℝ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ)))) :=
  ⟨(0 : ℕ), (0 : ℝ), (1 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ)))) :=
  ⟨(0 : ℕ), (0 : ℝ), (-1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ)))) :=
  ⟨(0 : ℕ), (1 : ℝ), (0 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ)))) :=
  ⟨(0 : ℕ), (1 : ℝ), (1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ)))) :=
  ⟨(0 : ℕ), (-1 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ)))) :=
  ⟨(1 : ℕ), (0 : ℝ), (0 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ)))) :=
  ⟨(1 : ℕ), (0 : ℝ), (1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ)))) :=
  ⟨(1 : ℕ), (1 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ)))) :=
  ⟨(2 : ℕ), (0 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ)))) :=
  ⟨(0 : ℕ), (0 : ℝ), (1 : ℝ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ)))) :=
  ⟨(0 : ℕ), (0 : ℝ), (-1 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ)))) :=
  ⟨(0 : ℕ), (1 : ℝ), (0 : ℝ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ)))) :=
  ⟨(0 : ℕ), (1 : ℝ), (1 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ)))) :=
  ⟨(0 : ℕ), (1 : ℝ), (-1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ)))) :=
  ⟨(0 : ℕ), (-1 : ℝ), (0 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ)))) :=
  ⟨(0 : ℕ), (-1 : ℝ), (1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ)))) :=
  ⟨(1 : ℕ), (0 : ℝ), (0 : ℝ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ)))) :=
  ⟨(1 : ℕ), (0 : ℝ), (1 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ)))) :=
  ⟨(1 : ℕ), (0 : ℝ), (-1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ)))) :=
  ⟨(1 : ℕ), (1 : ℝ), (0 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ)))) :=
  ⟨(1 : ℕ), (1 : ℝ), (1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ)))) :=
  ⟨(1 : ℕ), (-1 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ)))) :=
  ⟨(2 : ℕ), (0 : ℝ), (0 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ)))) :=
  ⟨(2 : ℕ), (0 : ℝ), (1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ)))) :=
  ⟨(2 : ℕ), (1 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ)))) :=
  ⟨(0 : ℕ), (0 : ℝ), (-1 : ℝ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ ((N : ℤ) > (p : ℤ))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) →
    (∀ (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi), (sievedSet N a lo hi).Nonempty) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi) :
    ((p : ℤ) ≤ (N : ℤ)) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi) :
    ((p : ℤ) ≤ (N : ℤ)) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi) :
    ((p : ℤ) ≤ (N : ℤ)) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi) :
    ((p : ℤ) ≤ (N : ℤ)) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi) :
    ((p : ℤ) ≤ (N : ℤ)) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi) :
    ((p : ℤ) ≤ (N : ℤ)) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi) :
    ((p : ℤ) ≤ (N : ℤ)) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℝ), (0 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℝ), (1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℝ), (0 : ℝ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℝ), (1 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℝ), (-1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℝ), (0 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℝ), (1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(0 : ℕ), (-1 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℝ), (0 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℝ), (1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℝ), (1 : ℝ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℝ), (-1 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℝ), (0 : ℝ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℝ), (1 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℝ), (-1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(0 : ℕ), (-1 : ℝ), (0 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(0 : ℕ), (-1 : ℝ), (1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℝ), (0 : ℝ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℝ), (1 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℝ), (-1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℝ), (0 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℝ), (1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(1 : ℕ), (-1 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℝ), (0 : ℝ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℝ), (1 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℝ), (0 : ℝ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (lo : ℝ) (hi : ℝ) (p : ℕ), (Nat.Prime p) ∧ (lo ≤ (p : ℝ)) ∧ ((p : ℝ) < hi) ∧ (¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℝ), (-1 : ℝ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ) (p : ℕ), ¬(((p : ℤ) ≤ (N : ℤ)) ↔ (True)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (N : ℕ) (a : ℕ → ℤ) (lo hi : ℝ) (p : ℕ) (hp : Nat.Prime p) (hpN : (p : ℤ) ≤ (N : ℤ)) (hlb : lo ≤ (p : ℝ)) (hub : (p : ℝ) < hi) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
