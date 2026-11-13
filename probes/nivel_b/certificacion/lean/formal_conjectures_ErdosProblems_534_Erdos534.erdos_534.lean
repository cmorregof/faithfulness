import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 534

*References:*
- [erdosproblems.com/534](https://www.erdosproblems.com/534)
- [Er73] Erdős, P., _Problems and results on combinatorial number theory_. A survey of
  combinatorial theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins, Colo., 1971)
  (1973), 117-138.
- [Er80] Erdős, Paul, _A survey of problems in combinatorial number theory_. Ann. Discrete Math.
  (1980), 89-115.
- [AhKh96] Ahlswede, Rudolf and Khachatrian, Levon H., _Sets of integers with pairwise common
  divisor and a factor from a specified set of primes_. Acta Arith. (1996), 259--276.
-/

section

namespace Erdos534

/-- A set `A ⊆ {1, …, N}` is *admissible* if it contains `N` and any two distinct elements
of `A` have a common factor. -/
def IsAdmissible (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧ N ∈ A ∧ (A : Set ℕ).Pairwise fun a b ↦ 1 < Nat.gcd a b

/-- The largest size of an admissible subset of `{1, …, N}`. -/
noncomputable def maxCard (N : ℕ) : ℕ :=
  sSup {n | ∃ A : Finset ℕ, IsAdmissible N A ∧ A.card = n}

/-- The prime factors `q₁ < ⋯ < qⱼ` of `N` which are at most `q`. -/
def primePrefix (N q : ℕ) : Finset ℕ := N.primeFactors.filter (· ≤ q)

/-- The Ahlswede–Khachatrian set associated to a prime factor `q` of `N`: those integers in
`[1, N]` which are a multiple of at least one of `2 q₁, …, 2 qⱼ, q₁ ⋯ qⱼ`, where
`q₁ < ⋯ < qⱼ = q` are the prime factors of `N` which are at most `q`. -/
def ahlswedeKhachatrian (N q : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun m ↦
    (∏ p ∈ primePrefix N q, p) ∣ m ∨ ∃ p ∈ primePrefix N q, 2 * p ∣ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (hN : 2 < N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) →
    (∀ (N : ℕ) (hN : 2 < N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) →
    (∀ (N : ℕ) (hN : 2 < N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) →
    (∀ (N : ℕ) (hN : 2 < N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) →
    (∀ (N : ℕ) (hN : 2 < N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) →
    (∀ (N : ℕ) (hN : 2 < N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) →
    (∀ (N : ℕ) (hN : 2 < N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) →
    (∀ (N : ℕ) (hN : 2 < N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (2 ≤ N) ↔ (2 < N) := by
  omega

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (2 ≤ N) ↔ (2 < N) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (2 ≤ N) ↔ (2 < N) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (2 ≤ N) ↔ (2 < N) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (2 ≤ N) ↔ (2 < N) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (2 ≤ N) ↔ (2 < N) := by
  simp_all

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (2 ≤ N) ↔ (2 < N) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((2 ≤ N) ↔ (2 < N))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((2 ≤ N) ↔ (2 < N))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((2 ≤ N) ↔ (2 < N))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((2 ≤ N) ↔ (2 < N))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((2 ≤ N) ↔ (2 < N))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((2 ≤ N) ↔ (2 < N))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((2 ≤ N) ↔ (2 < N)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((2 ≤ N) ↔ (2 < N)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((2 ≤ N) ↔ (2 < N)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((2 ≤ N) ↔ (2 < N)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((2 ≤ N) ↔ (2 < N)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((2 ≤ N) ↔ (2 < N)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (hN : 3 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) →
    (∀ (N : ℕ) (hN : 3 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) →
    (∀ (N : ℕ) (hN : 3 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) →
    (∀ (N : ℕ) (hN : 3 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) →
    (∀ (N : ℕ) (hN : 3 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) →
    (∀ (N : ℕ) (hN : 3 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) →
    (∀ (N : ℕ) (hN : 3 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) →
    (∀ (N : ℕ) (hN : 3 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (2 ≤ N) ↔ (3 ≤ N) := by
  omega

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (2 ≤ N) ↔ (3 ≤ N) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (2 ≤ N) ↔ (3 ≤ N) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (2 ≤ N) ↔ (3 ≤ N) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (2 ≤ N) ↔ (3 ≤ N) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (2 ≤ N) ↔ (3 ≤ N) := by
  simp_all

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (2 ≤ N) ↔ (3 ≤ N) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((2 ≤ N) ↔ (3 ≤ N))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((2 ≤ N) ↔ (3 ≤ N))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((2 ≤ N) ↔ (3 ≤ N))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((2 ≤ N) ↔ (3 ≤ N))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((2 ≤ N) ↔ (3 ≤ N))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((2 ≤ N) ↔ (3 ≤ N))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((2 ≤ N) ↔ (3 ≤ N))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((2 ≤ N) ↔ (3 ≤ N)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((2 ≤ N) ↔ (3 ≤ N)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((2 ≤ N) ↔ (3 ≤ N)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((2 ≤ N) ↔ (3 ≤ N)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((2 ≤ N) ↔ (3 ≤ N)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((2 ≤ N) ↔ (3 ≤ N)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((2 ≤ N) ↔ (3 ≤ N)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (hN : N ≥ 2), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (2 ≤ N) ↔ (N ≥ 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (2 ≤ N) ↔ (N ≥ 2) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (2 ≤ N) ↔ (N ≥ 2) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (2 ≤ N) ↔ (N ≥ 2) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (2 ≤ N) ↔ (N ≥ 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (2 ≤ N) ↔ (N ≥ 2) := by
  omega

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (2 ≤ N) ↔ (N ≥ 2) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (2 ≤ N) ↔ (N ≥ 2) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) ↔
    (∀ (N : ℕ) (hN : N ≥ 2), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) ↔
    (∀ (N : ℕ) (hN : N ≥ 2), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) ↔
    (∀ (N : ℕ) (hN : N ≥ 2), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) ↔
    (∀ (N : ℕ) (hN : N ≥ 2), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (hN₀ : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) ↔
    (∀ (N : ℕ) (hN₀ : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) ↔
    (∀ (N : ℕ) (hN₀ : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) ↔
    (∀ (N : ℕ) (hN₀ : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) ↔
    (∀ (N : ℕ) (hN₀ : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (hN : ¬(N < 2)), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (2 ≤ N) ↔ (¬(N < 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (2 ≤ N) ↔ (¬(N < 2)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (2 ≤ N) ↔ (¬(N < 2)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (2 ≤ N) ↔ (¬(N < 2)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (2 ≤ N) ↔ (¬(N < 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (2 ≤ N) ↔ (¬(N < 2)) := by
  omega

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (2 ≤ N) ↔ (¬(N < 2)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (2 ≤ N) ↔ (¬(N < 2)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) ↔
    (∀ (N : ℕ) (hN : ¬(N < 2)), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) ↔
    (∀ (N : ℕ) (hN : ¬(N < 2)), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) ↔
    (∀ (N : ℕ) (hN : ¬(N < 2)), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) ↔
    (∀ (N : ℕ) (hN : ¬(N < 2)), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (hN : 1 < N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (2 ≤ N) ↔ (1 < N) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (2 ≤ N) ↔ (1 < N) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (2 ≤ N) ↔ (1 < N) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (2 ≤ N) ↔ (1 < N) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (2 ≤ N) ↔ (1 < N) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (2 ≤ N) ↔ (1 < N) := by
  omega

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (2 ≤ N) ↔ (1 < N) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (2 ≤ N) ↔ (1 < N) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) ↔
    (∀ (N : ℕ) (hN : 1 < N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) ↔
    (∀ (N : ℕ) (hN : 1 < N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) ↔
    (∀ (N : ℕ) (hN : 1 < N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) ↔
    (∀ (N : ℕ) (hN : 1 < N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (hN : N > 2), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) →
    (∀ (N : ℕ) (hN : N > 2), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) →
    (∀ (N : ℕ) (hN : N > 2), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) →
    (∀ (N : ℕ) (hN : N > 2), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) →
    (∀ (N : ℕ) (hN : N > 2), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) →
    (∀ (N : ℕ) (hN : N > 2), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) →
    (∀ (N : ℕ) (hN : N > 2), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) →
    (∀ (N : ℕ) (hN : N > 2), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (2 ≤ N) ↔ (N > 2) := by
  omega

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (2 ≤ N) ↔ (N > 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (2 ≤ N) ↔ (N > 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (2 ≤ N) ↔ (N > 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (2 ≤ N) ↔ (N > 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (2 ≤ N) ↔ (N > 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (2 ≤ N) ↔ (N > 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((2 ≤ N) ↔ (N > 2))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((2 ≤ N) ↔ (N > 2))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((2 ≤ N) ↔ (N > 2))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((2 ≤ N) ↔ (N > 2))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((2 ≤ N) ↔ (N > 2))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((2 ≤ N) ↔ (N > 2))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((2 ≤ N) ↔ (N > 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((2 ≤ N) ↔ (N > 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((2 ≤ N) ↔ (N > 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((2 ≤ N) ↔ (N > 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((2 ≤ N) ↔ (N > 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((2 ≤ N) ↔ (N > 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (hN : N ≥ 3), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) →
    (∀ (N : ℕ) (hN : N ≥ 3), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) →
    (∀ (N : ℕ) (hN : N ≥ 3), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) →
    (∀ (N : ℕ) (hN : N ≥ 3), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) →
    (∀ (N : ℕ) (hN : N ≥ 3), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) →
    (∀ (N : ℕ) (hN : N ≥ 3), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) →
    (∀ (N : ℕ) (hN : N ≥ 3), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) →
    (∀ (N : ℕ) (hN : N ≥ 3), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (2 ≤ N) ↔ (N ≥ 3) := by
  omega

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (2 ≤ N) ↔ (N ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (2 ≤ N) ↔ (N ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (2 ≤ N) ↔ (N ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (2 ≤ N) ↔ (N ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (2 ≤ N) ↔ (N ≥ 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (2 ≤ N) ↔ (N ≥ 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((2 ≤ N) ↔ (N ≥ 3))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((2 ≤ N) ↔ (N ≥ 3))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((2 ≤ N) ↔ (N ≥ 3))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((2 ≤ N) ↔ (N ≥ 3))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((2 ≤ N) ↔ (N ≥ 3))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((2 ≤ N) ↔ (N ≥ 3))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((2 ≤ N) ↔ (N ≥ 3))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((2 ≤ N) ↔ (N ≥ 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((2 ≤ N) ↔ (N ≥ 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((2 ≤ N) ↔ (N ≥ 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((2 ≤ N) ↔ (N ≥ 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((2 ≤ N) ↔ (N ≥ 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((2 ≤ N) ↔ (N ≥ 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((2 ≤ N) ↔ (N ≥ 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (hN : 1 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) →
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) →
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) →
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) →
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) →
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) →
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) →
    (∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (2 ≤ N) ↔ (1 ≤ N) := by
  omega

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (2 ≤ N) ↔ (1 ≤ N) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (2 ≤ N) ↔ (1 ≤ N) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (2 ≤ N) ↔ (1 ≤ N) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (2 ≤ N) ↔ (1 ≤ N) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (2 ≤ N) ↔ (1 ≤ N) := by
  simp_all

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (2 ≤ N) ↔ (1 ≤ N) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((2 ≤ N) ↔ (1 ≤ N))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((2 ≤ N) ↔ (1 ≤ N))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((2 ≤ N) ↔ (1 ≤ N))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((2 ≤ N) ↔ (1 ≤ N))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((2 ≤ N) ↔ (1 ≤ N))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((2 ≤ N) ↔ (1 ≤ N))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((2 ≤ N) ↔ (1 ≤ N)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((2 ≤ N) ↔ (1 ≤ N)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((2 ≤ N) ↔ (1 ≤ N)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((2 ≤ N) ↔ (1 ≤ N)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((2 ≤ N) ↔ (1 ≤ N)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((2 ≤ N) ↔ (1 ≤ N)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (N : ℕ) (hN : 2 ≤ N) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (N : ℕ) (hN : 2 ≤ N) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (N : ℕ) (hN : 2 ≤ N) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (N : ℕ) (hN : 2 ≤ N) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (N : ℕ) (hN : 2 ≤ N) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
