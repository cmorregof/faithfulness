import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 535

*References:*
- [erdosproblems.com/535](https://www.erdosproblems.com/535)
- [Er64] P. Erdős, _On a problem in elementary number theory and a combinatorial problem_. Math.
  Comp. (1964), 644–646.
- [AbHa70] H. L. Abbott and D. Hanson, _An extremal problem in number theory_. Bull. London Math.
  Soc. (1970), 324–326.
- [Er73] P. Erdős, _Problems and results on combinatorial number theory_, in
  *A Survey of Combinatorial Theory*, North-Holland, 1973.
-/

section

open ArithmeticFunction
open Filter Real
open scoped omega Omega

namespace Erdos535

/-- No `r`-subset has constant pairwise GCD with coprime quotients. -/
def NoConstantPairwiseGcdCoprimeSubsets (r : ℕ) (A : Finset ℕ) : Prop :=
  ∀ S ⊆ A, S.card = r →
    ¬ (∃ d, 0 < d ∧ (S : Set ℕ).Pairwise (fun a b => Nat.gcd a b = d) ∧
      ∀ a ∈ S, ∃ b, a = d * b ∧ Nat.gcd b d = 1)

/--
All elements of `A` are positive and have exactly `k` prime factors,
counted with multiplicity.

Erdős [Er73] explains that Abbott pointed out the ordinary sunflower conjecture
does not seem to suffice for Problem 535; the corrected stronger auxiliary
statement uses $Ω$, not $ω$.
-/
def AllBigOmega (k : ℕ) (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, 1 ≤ a ∧ Ω a = k

/-- `f r N` is the maximum size of a subset `A ⊆ {1,…,N}` such that no `r`-element
subset of `A` has constant pairwise GCD. -/
noncomputable def f (r N : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
    (∀ S ⊆ A, S.card = r →
      ¬ (∃ d, (S : Set ℕ).Pairwise fun a b => Nat.gcd a b = d)) ∧
    A.card = k}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {r : ℕ} (hr : 3 < r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)

set_option maxHeartbeats 200000 in
example :
    (∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) →
    (∀ {r : ℕ} (hr : 3 < r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) →
    (∀ {r : ℕ} (hr : 3 < r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) →
    (∀ {r : ℕ} (hr : 3 < r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) →
    (∀ {r : ℕ} (hr : 3 < r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) →
    (∀ {r : ℕ} (hr : 3 < r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) →
    (∀ {r : ℕ} (hr : 3 < r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) →
    (∀ {r : ℕ} (hr : 3 < r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {r : ℕ}  :
    (3 ≤ r) ↔ (3 < r) := by
  omega

set_option maxHeartbeats 200000 in
example {r : ℕ}  :
    (3 ≤ r) ↔ (3 < r) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {r : ℕ}  :
    (3 ≤ r) ↔ (3 < r) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {r : ℕ}  :
    (3 ≤ r) ↔ (3 < r) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {r : ℕ}  :
    (3 ≤ r) ↔ (3 < r) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {r : ℕ}  :
    (3 ≤ r) ↔ (3 < r) := by
  simp_all

set_option maxHeartbeats 200000 in
example {r : ℕ}  :
    (3 ≤ r) ↔ (3 < r) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (3 < r))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (3 < r))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (3 < r))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (3 < r))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (3 < r))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (3 < r))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (3 < r))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (3 < r)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (3 < r)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (3 < r)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (3 < r)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (3 < r)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (3 < r)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (3 < r)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {r : ℕ} (hr : r ≥ 3), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)

set_option maxHeartbeats 200000 in
example {r : ℕ} :
    (3 ≤ r) ↔ (r ≥ 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {r : ℕ} :
    (3 ≤ r) ↔ (r ≥ 3) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {r : ℕ} :
    (3 ≤ r) ↔ (r ≥ 3) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {r : ℕ} :
    (3 ≤ r) ↔ (r ≥ 3) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {r : ℕ} :
    (3 ≤ r) ↔ (r ≥ 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {r : ℕ} :
    (3 ≤ r) ↔ (r ≥ 3) := by
  omega

set_option maxHeartbeats 200000 in
example {r : ℕ} :
    (3 ≤ r) ↔ (r ≥ 3) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {r : ℕ} :
    (3 ≤ r) ↔ (r ≥ 3) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) ↔
    (∀ {r : ℕ} (hr : r ≥ 3), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) ↔
    (∀ {r : ℕ} (hr : r ≥ 3), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) ↔
    (∀ {r : ℕ} (hr : r ≥ 3), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) ↔
    (∀ {r : ℕ} (hr : r ≥ 3), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r₁ > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r₁ ^ k * (Nat.factorial k)

set_option maxHeartbeats 200000 in
example {r : ℕ} :
    (∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) ↔ (∃ c_r₁ > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r₁ ^ k * (Nat.factorial k)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {r : ℕ} :
    (∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) ↔ (∃ c_r₁ > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r₁ ^ k * (Nat.factorial k)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {r : ℕ} :
    (∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) ↔ (∃ c_r₁ > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r₁ ^ k * (Nat.factorial k)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {r : ℕ} :
    (∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) ↔ (∃ c_r₁ > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r₁ ^ k * (Nat.factorial k)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {r : ℕ} :
    (∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) ↔ (∃ c_r₁ > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r₁ ^ k * (Nat.factorial k)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {r : ℕ} :
    (∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) ↔ (∃ c_r₁ > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r₁ ^ k * (Nat.factorial k)) := by
  omega

set_option maxHeartbeats 200000 in
example {r : ℕ} :
    (∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) ↔ (∃ c_r₁ > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r₁ ^ k * (Nat.factorial k)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {r : ℕ} :
    (∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) ↔ (∃ c_r₁ > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r₁ ^ k * (Nat.factorial k)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) ↔
    (∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r₁ > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r₁ ^ k * (Nat.factorial k)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) ↔
    (∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r₁ > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r₁ ^ k * (Nat.factorial k)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) ↔
    (∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r₁ > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r₁ ^ k * (Nat.factorial k)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) ↔
    (∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r₁ > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r₁ ^ k * (Nat.factorial k)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {r : ℕ} (hr₀ : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)

set_option maxHeartbeats 200000 in
example :
    (∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) ↔
    (∀ {r : ℕ} (hr₀ : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) ↔
    (∀ {r : ℕ} (hr₀ : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) ↔
    (∀ {r : ℕ} (hr₀ : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) ↔
    (∀ {r : ℕ} (hr₀ : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {r : ℕ} (hr : ¬(r < 3)), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)

set_option maxHeartbeats 200000 in
example {r : ℕ} :
    (3 ≤ r) ↔ (¬(r < 3)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {r : ℕ} :
    (3 ≤ r) ↔ (¬(r < 3)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {r : ℕ} :
    (3 ≤ r) ↔ (¬(r < 3)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {r : ℕ} :
    (3 ≤ r) ↔ (¬(r < 3)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {r : ℕ} :
    (3 ≤ r) ↔ (¬(r < 3)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {r : ℕ} :
    (3 ≤ r) ↔ (¬(r < 3)) := by
  omega

set_option maxHeartbeats 200000 in
example {r : ℕ} :
    (3 ≤ r) ↔ (¬(r < 3)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {r : ℕ} :
    (3 ≤ r) ↔ (¬(r < 3)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) ↔
    (∀ {r : ℕ} (hr : ¬(r < 3)), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) ↔
    (∀ {r : ℕ} (hr : ¬(r < 3)), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) ↔
    (∀ {r : ℕ} (hr : ¬(r < 3)), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) ↔
    (∀ {r : ℕ} (hr : ¬(r < 3)), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {r : ℕ} (hr : 2 < r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)

set_option maxHeartbeats 200000 in
example {r : ℕ} :
    (3 ≤ r) ↔ (2 < r) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {r : ℕ} :
    (3 ≤ r) ↔ (2 < r) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {r : ℕ} :
    (3 ≤ r) ↔ (2 < r) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {r : ℕ} :
    (3 ≤ r) ↔ (2 < r) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {r : ℕ} :
    (3 ≤ r) ↔ (2 < r) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {r : ℕ} :
    (3 ≤ r) ↔ (2 < r) := by
  omega

set_option maxHeartbeats 200000 in
example {r : ℕ} :
    (3 ≤ r) ↔ (2 < r) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {r : ℕ} :
    (3 ≤ r) ↔ (2 < r) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) ↔
    (∀ {r : ℕ} (hr : 2 < r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) ↔
    (∀ {r : ℕ} (hr : 2 < r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) ↔
    (∀ {r : ℕ} (hr : 2 < r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) ↔
    (∀ {r : ℕ} (hr : 2 < r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {r : ℕ} (hr : r > 3), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)

set_option maxHeartbeats 200000 in
example :
    (∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) →
    (∀ {r : ℕ} (hr : r > 3), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) →
    (∀ {r : ℕ} (hr : r > 3), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) →
    (∀ {r : ℕ} (hr : r > 3), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) →
    (∀ {r : ℕ} (hr : r > 3), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) →
    (∀ {r : ℕ} (hr : r > 3), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) →
    (∀ {r : ℕ} (hr : r > 3), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) →
    (∀ {r : ℕ} (hr : r > 3), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {r : ℕ}  :
    (3 ≤ r) ↔ (r > 3) := by
  omega

set_option maxHeartbeats 200000 in
example {r : ℕ}  :
    (3 ≤ r) ↔ (r > 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {r : ℕ}  :
    (3 ≤ r) ↔ (r > 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {r : ℕ}  :
    (3 ≤ r) ↔ (r > 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {r : ℕ}  :
    (3 ≤ r) ↔ (r > 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {r : ℕ}  :
    (3 ≤ r) ↔ (r > 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example {r : ℕ}  :
    (3 ≤ r) ↔ (r > 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (r > 3))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (r > 3))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (r > 3))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (r > 3))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (r > 3))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (r > 3))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (r > 3))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (r > 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (r > 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (r > 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (r > 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (r > 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (r > 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (r > 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {r : ℕ} (hr : 2 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)

set_option maxHeartbeats 200000 in
example :
    (∀ {r : ℕ} (hr : 2 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) →
    (∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {r : ℕ} (hr : 2 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) →
    (∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {r : ℕ} (hr : 2 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) →
    (∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {r : ℕ} (hr : 2 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) →
    (∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {r : ℕ} (hr : 2 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) →
    (∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {r : ℕ} (hr : 2 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) →
    (∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {r : ℕ} (hr : 2 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) →
    (∀ {r : ℕ} (hr : 3 ≤ r), ∃ c_r > (0 : ℝ),
      ∀ k : ℕ, ∀ A : Finset ℕ,
        AllBigOmega k A →
        NoConstantPairwiseGcdCoprimeSubsets r A →
        (A.card : ℝ) ≤ c_r ^ k * (Nat.factorial k)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {r : ℕ}  :
    (3 ≤ r) ↔ (2 ≤ r) := by
  omega

set_option maxHeartbeats 200000 in
example {r : ℕ}  :
    (3 ≤ r) ↔ (2 ≤ r) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {r : ℕ}  :
    (3 ≤ r) ↔ (2 ≤ r) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {r : ℕ}  :
    (3 ≤ r) ↔ (2 ≤ r) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {r : ℕ}  :
    (3 ≤ r) ↔ (2 ≤ r) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {r : ℕ}  :
    (3 ≤ r) ↔ (2 ≤ r) := by
  simp_all

set_option maxHeartbeats 200000 in
example {r : ℕ}  :
    (3 ≤ r) ↔ (2 ≤ r) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (2 ≤ r))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (2 ≤ r))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (2 ≤ r))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (2 ≤ r))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (2 ≤ r))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (2 ≤ r))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (2 ≤ r))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (2 ≤ r)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (2 ≤ r)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (2 ≤ r)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (2 ≤ r)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (2 ≤ r)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (2 ≤ r)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (2 ≤ r)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {r : ℕ} (hr : 3 ≤ r) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {r : ℕ} (hr : 3 ≤ r) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {r : ℕ} (hr : 3 ≤ r) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {r : ℕ} (hr : 3 ≤ r) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {r : ℕ} (hr : 3 ≤ r) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
