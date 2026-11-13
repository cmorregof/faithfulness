import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Data.Set.Density
/-!
# Erdős Problem 690

*References:*
- [erdosproblems.com/690](https://www.erdosproblems.com/690)
- [Er79e] Erdős, Paul, _Some unconventional problems in number theory_. Astérisque (1979), 73-82.
- [Ca25] S. Cambie, _Resolution of Erdős' problems about unimodularity_. arXiv:2501.10333 (2025).
- [WC26] S. Wang and D. Crapis, _A Complete Answer to Erdős Problem 690_. arXiv:2605.08542 (2026).
-/

section

open Filter

namespace Erdos690

/-- The set of positive integers whose `k`-th smallest prime factor is `p`: if
$p_1<p_2<\cdots$ are the primes dividing $n$ then $p_k=p$. -/
def kthPrimeFactorSet (k p : ℕ) : Set ℕ :=
  {n | 0 < n ∧ p ∈ n.primeFactors ∧ (n.primeFactors.filter (· < p)).card = k - 1}

/-- A function on the primes is *unimodular* if it first increases in $p$ until its maximum then
decreases. -/
def IsUnimodalOnPrimes (f : ℕ → ℝ) : Prop :=
  ∃ m, m.Prime ∧ (∀ p q, p.Prime → q.Prime → p ≤ q → q ≤ m → f p ≤ f q) ∧
    ∀ p q, p.Prime → q.Prime → m ≤ p → p ≤ q → f q ≤ f p

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 3) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (1 ≤ k) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 3) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (1 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 3) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (1 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 3) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (1 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 3) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (1 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 3) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (1 ≤ k) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 3) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (1 ≤ k) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 < k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 1 < k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 1 < k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 1 < k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 1 < k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 1 < k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 1 < k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 1 < k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 3) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (1 ≤ k) ↔ (1 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 3) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (1 ≤ k) ↔ (1 < k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 3) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (1 ≤ k) ↔ (1 < k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 3) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (1 ≤ k) ↔ (1 < k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 3) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (1 ≤ k) ↔ (1 < k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 3) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (1 ≤ k) ↔ (1 < k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 3) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (1 ≤ k) ↔ (1 < k) := by
  plausible

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
  ∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 4) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 4) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 4) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 4) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 4) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 4) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 4) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 4) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 1 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 3) ↔ (k ≤ 4) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 1 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 3) ↔ (k ≤ 4) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 1 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 3) ↔ (k ≤ 4) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 1 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 3) ↔ (k ≤ 4) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 1 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 3) ↔ (k ≤ 4) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 1 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 3) ↔ (k ≤ 4) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 1 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 3) ↔ (k ≤ 4) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 3) ↔ (k ≤ 4)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 3) ↔ (k ≤ 4)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 3) ↔ (k ≤ 4)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 3) ↔ (k ≤ 4)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 3) ↔ (k ≤ 4)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 3) ↔ (k ≤ 4)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 3) ↔ (k ≤ 4)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 1) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) ↔
    (∀ (k : ℕ) (hk : k ≥ 1) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) ↔
    (∀ (k : ℕ) (hk : k ≥ 1) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) ↔
    (∀ (k : ℕ) (hk : k ≥ 1) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) ↔
    (∀ (k : ℕ) (hk : k ≥ 1) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk' : k ≤ 3) (hk : 1 ≤ k) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) ↔
    (∀ (k : ℕ) (hk' : k ≤ 3) (hk : 1 ≤ k) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) ↔
    (∀ (k : ℕ) (hk' : k ≤ 3) (hk : 1 ≤ k) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) ↔
    (∀ (k : ℕ) (hk' : k ≤ 3) (hk : 1 ≤ k) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) ↔
    (∀ (k : ℕ) (hk' : k ≤ 3) (hk : 1 ≤ k) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk₀ : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) ↔
    (∀ (k : ℕ) (hk₀ : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) ↔
    (∀ (k : ℕ) (hk₀ : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) ↔
    (∀ (k : ℕ) (hk₀ : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) ↔
    (∀ (k : ℕ) (hk₀ : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : ¬(k < 1)) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) ↔
    (∀ (k : ℕ) (hk : ¬(k < 1)) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) ↔
    (∀ (k : ℕ) (hk : ¬(k < 1)) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) ↔
    (∀ (k : ℕ) (hk : ¬(k < 1)) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) ↔
    (∀ (k : ℕ) (hk : ¬(k < 1)) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 0 < k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (1 ≤ k) ↔ (0 < k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (1 ≤ k) ↔ (0 < k) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (1 ≤ k) ↔ (0 < k) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (1 ≤ k) ↔ (0 < k) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (1 ≤ k) ↔ (0 < k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (1 ≤ k) ↔ (0 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (1 ≤ k) ↔ (0 < k) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (1 ≤ k) ↔ (0 < k) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) ↔
    (∀ (k : ℕ) (hk : 0 < k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) ↔
    (∀ (k : ℕ) (hk : 0 < k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) ↔
    (∀ (k : ℕ) (hk : 0 < k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) ↔
    (∀ (k : ℕ) (hk : 0 < k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k > 1) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : k > 1) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : k > 1) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : k > 1) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : k > 1) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : k > 1) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : k > 1) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : k > 1) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 3) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (1 ≤ k) ↔ (k > 1) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 3) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (1 ≤ k) ↔ (k > 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 3) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (1 ≤ k) ↔ (k > 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 3) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (1 ≤ k) ↔ (k > 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 3) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (1 ≤ k) ↔ (k > 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 3) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (1 ≤ k) ↔ (k > 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 3) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (1 ≤ k) ↔ (k > 1) := by
  plausible

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
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 1) (hk' : k ≤ 4) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 1) (hk' : k ≤ 4) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 1) (hk' : k ≤ 4) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 1) (hk' : k ≤ 4) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 1) (hk' : k ≤ 4) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 1) (hk' : k ≤ 4) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 1) (hk' : k ≤ 4) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 1) (hk' : k ≤ 4) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 1 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 3) ↔ (k ≤ 4) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 1 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 3) ↔ (k ≤ 4) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 1 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 3) ↔ (k ≤ 4) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 1 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 3) ↔ (k ≤ 4) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 1 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 3) ↔ (k ≤ 4) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 1 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 3) ↔ (k ≤ 4) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 1 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 3) ↔ (k ≤ 4) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 3) ↔ (k ≤ 4)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 3) ↔ (k ≤ 4)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 3) ↔ (k ≤ 4)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 3) ↔ (k ≤ 4)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 3) ↔ (k ≤ 4)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 3) ↔ (k ≤ 4)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 3) ↔ (k ≤ 4)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 0 < k) (hk' : k < 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 0 < k) (hk' : k < 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 0 < k) (hk' : k < 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 0 < k) (hk' : k < 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 0 < k) (hk' : k < 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 0 < k) (hk' : k < 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 0 < k) (hk' : k < 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 0 < k) (hk' : k < 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 1 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 3) ↔ (k < 3) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 1 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 3) ↔ (k < 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 1 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 3) ↔ (k < 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 1 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 3) ↔ (k < 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 1 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 3) ↔ (k < 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 1 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 3) ↔ (k < 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 1 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 3) ↔ (k < 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 3) ↔ (k < 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 3) ↔ (k < 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 3) ↔ (k < 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 3) ↔ (k < 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 3) ↔ (k < 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 3) ↔ (k < 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 3) ↔ (k < 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 0 < k) (hk' : k ≤ 4) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (hk' : k ≤ 4) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (hk' : k ≤ 4) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (hk' : k ≤ 4) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (hk' : k ≤ 4) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (hk' : k ≤ 4) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (hk' : k ≤ 4) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (hk' : k ≤ 4) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 1 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 3) ↔ (k ≤ 4) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 1 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 3) ↔ (k ≤ 4) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 1 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 3) ↔ (k ≤ 4) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 1 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 3) ↔ (k ≤ 4) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 1 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 3) ↔ (k ≤ 4) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 1 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 3) ↔ (k ≤ 4) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 1 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 3) ↔ (k ≤ 4) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 3) ↔ (k ≤ 4)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 3) ↔ (k ≤ 4)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 3) ↔ (k ≤ 4)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 3) ↔ (k ≤ 4)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 3) ↔ (k ≤ 4)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 3) ↔ (k ≤ 4)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 3) ↔ (k ≤ 4)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 3) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), IsUnimodalOnPrimes d) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 1 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 3) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 1 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 3) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 1 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 3) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 1 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 3) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 1 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 3) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 1 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 3) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 1 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 3) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 3) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 3) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 3) ↔ (True)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 3) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 3) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 3) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 3) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 1 ≤ k) (hk' : k ≤ 3) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 1 ≤ k) (hk' : k ≤ 3) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 1 ≤ k) (hk' : k ≤ 3) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 1 ≤ k) (hk' : k ≤ 3) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 1 ≤ k) (hk' : k ≤ 3) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
