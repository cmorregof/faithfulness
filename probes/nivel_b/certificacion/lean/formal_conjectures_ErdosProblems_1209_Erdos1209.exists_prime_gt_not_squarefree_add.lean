import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 1209

*References:*
- [erdosproblems.com/429](https://www.erdosproblems.com/429)
- [erdosproblems.com/1102](https://www.erdosproblems.com/1102)
- [erdosproblems.com/1209](https://www.erdosproblems.com/1209)
- [Er80] Erdős, Paul, A survey of problems in combinatorial number theory. Ann. Discrete Math.
  (1980), 89-115.
-/

section

open Nat Set

namespace Erdos1209

/-- For every `k ≥ 1` and bound `m`, there is a prime `p > m` such that `k + p` is composite:
take a prime `q > k` and, by Dirichlet, a prime `p > max m q` with `p ≡ -k (mod q)`. -/
theorem exists_prime_gt_not_prime_add (k m : ℕ) (hk : 1 ≤ k) :
    ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime := by
  obtain ⟨q, hqk, hq⟩ := Nat.exists_infinite_primes (k + 1)
  have : NeZero q := ⟨hq.ne_zero⟩
  have hunit : IsUnit (-(k : ZMod q)) := by
    refine IsUnit.neg ?_
    rw [ZMod.isUnit_iff_coprime]
    exact (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hq).2
      (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))))
  obtain ⟨p, hp, hpp, hpq⟩ := Nat.forall_exists_prime_gt_and_eq_mod hunit (max m q)
  refine ⟨p, by omega, hpp, ?_⟩
  have hdvd : q ∣ k + p := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, hpq]
    ring
  exact Nat.not_prime_of_dvd_of_lt hdvd hq.two_le (by omega)

/-- The counterexample sequence: `a 0` is a prime at least `f 0`, and `a (k + 1)` is a prime
larger than `a k` and `f (k + 1)` with `(k + 1) + a (k + 1)` composite. -/
noncomputable def seq (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => Classical.choose (Nat.exists_infinite_primes (f 0))
  | k + 1 => Classical.choose (exists_prime_gt_not_prime_add (k + 1) (max (seq f k) (f (k + 1)))
      (by omega))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m : ℕ) (hk : 1 < k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) →
    (∀ (k m : ℕ) (hk : 1 < k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) →
    (∀ (k m : ℕ) (hk : 1 < k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) →
    (∀ (k m : ℕ) (hk : 1 < k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) →
    (∀ (k m : ℕ) (hk : 1 < k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) →
    (∀ (k m : ℕ) (hk : 1 < k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) →
    (∀ (k m : ℕ) (hk : 1 < k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) →
    (∀ (k m : ℕ) (hk : 1 < k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k m : ℕ)  :
    (1 ≤ k) ↔ (1 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (k m : ℕ)  :
    (1 ≤ k) ↔ (1 < k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k m : ℕ)  :
    (1 ≤ k) ↔ (1 < k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k m : ℕ)  :
    (1 ≤ k) ↔ (1 < k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k m : ℕ)  :
    (1 ≤ k) ↔ (1 < k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k m : ℕ)  :
    (1 ≤ k) ↔ (1 < k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k m : ℕ)  :
    (1 ≤ k) ↔ (1 < k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (1 < k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (1 < k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (1 < k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (1 < k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (1 < k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (1 < k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m : ℕ) (hk : k ≥ 1), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) ↔
    (∀ (k m : ℕ) (hk : k ≥ 1), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) ↔
    (∀ (k m : ℕ) (hk : k ≥ 1), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) ↔
    (∀ (k m : ℕ) (hk : k ≥ 1), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) ↔
    (∀ (k m : ℕ) (hk : k ≥ 1), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p₁, m < p₁ ∧ p₁.Prime ∧ ¬ Squarefree (k + p₁)

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) ↔ (∃ p₁, m < p₁ ∧ p₁.Prime ∧ ¬ Squarefree (k + p₁)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) ↔ (∃ p₁, m < p₁ ∧ p₁.Prime ∧ ¬ Squarefree (k + p₁)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) ↔ (∃ p₁, m < p₁ ∧ p₁.Prime ∧ ¬ Squarefree (k + p₁)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) ↔ (∃ p₁, m < p₁ ∧ p₁.Prime ∧ ¬ Squarefree (k + p₁)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) ↔ (∃ p₁, m < p₁ ∧ p₁.Prime ∧ ¬ Squarefree (k + p₁)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) ↔ (∃ p₁, m < p₁ ∧ p₁.Prime ∧ ¬ Squarefree (k + p₁)) := by
  omega

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) ↔ (∃ p₁, m < p₁ ∧ p₁.Prime ∧ ¬ Squarefree (k + p₁)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) ↔ (∃ p₁, m < p₁ ∧ p₁.Prime ∧ ¬ Squarefree (k + p₁)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) ↔
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p₁, m < p₁ ∧ p₁.Prime ∧ ¬ Squarefree (k + p₁)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) ↔
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p₁, m < p₁ ∧ p₁.Prime ∧ ¬ Squarefree (k + p₁)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) ↔
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p₁, m < p₁ ∧ p₁.Prime ∧ ¬ Squarefree (k + p₁)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) ↔
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p₁, m < p₁ ∧ p₁.Prime ∧ ¬ Squarefree (k + p₁)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m : ℕ) (hk₀ : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) ↔
    (∀ (k m : ℕ) (hk₀ : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) ↔
    (∀ (k m : ℕ) (hk₀ : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) ↔
    (∀ (k m : ℕ) (hk₀ : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) ↔
    (∀ (k m : ℕ) (hk₀ : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m : ℕ) (hk : ¬(k < 1)), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  omega

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) ↔
    (∀ (k m : ℕ) (hk : ¬(k < 1)), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) ↔
    (∀ (k m : ℕ) (hk : ¬(k < 1)), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) ↔
    (∀ (k m : ℕ) (hk : ¬(k < 1)), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) ↔
    (∀ (k m : ℕ) (hk : ¬(k < 1)), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m : ℕ) (hk : 0 < k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (0 < k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (0 < k) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (0 < k) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (0 < k) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (0 < k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (0 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (0 < k) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k m : ℕ) :
    (1 ≤ k) ↔ (0 < k) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) ↔
    (∀ (k m : ℕ) (hk : 0 < k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) ↔
    (∀ (k m : ℕ) (hk : 0 < k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) ↔
    (∀ (k m : ℕ) (hk : 0 < k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) ↔
    (∀ (k m : ℕ) (hk : 0 < k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m : ℕ) (hk : k > 1), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) →
    (∀ (k m : ℕ) (hk : k > 1), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) →
    (∀ (k m : ℕ) (hk : k > 1), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) →
    (∀ (k m : ℕ) (hk : k > 1), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) →
    (∀ (k m : ℕ) (hk : k > 1), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) →
    (∀ (k m : ℕ) (hk : k > 1), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) →
    (∀ (k m : ℕ) (hk : k > 1), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k m : ℕ) (hk : 1 ≤ k), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) →
    (∀ (k m : ℕ) (hk : k > 1), ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k m : ℕ)  :
    (1 ≤ k) ↔ (k > 1) := by
  omega

set_option maxHeartbeats 200000 in
example (k m : ℕ)  :
    (1 ≤ k) ↔ (k > 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k m : ℕ)  :
    (1 ≤ k) ↔ (k > 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k m : ℕ)  :
    (1 ≤ k) ↔ (k > 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k m : ℕ)  :
    (1 ≤ k) ↔ (k > 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k m : ℕ)  :
    (1 ≤ k) ↔ (k > 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k m : ℕ)  :
    (1 ≤ k) ↔ (k > 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (k > 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (k > 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (k > 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (k > 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (k > 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (k > 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (k m : ℕ) (hk : 1 ≤ k) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (k m : ℕ) (hk : 1 ≤ k) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (k m : ℕ) (hk : 1 ≤ k) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (k m : ℕ) (hk : 1 ≤ k) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (k m : ℕ) (hk : 1 ≤ k) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
