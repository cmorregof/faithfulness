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
  ∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (4 ≤ k) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (4 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (4 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (4 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (4 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (4 ≤ k) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (4 ≤ k) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (True)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 < k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 4 < k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 4 < k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 4 < k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 4 < k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 4 < k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 4 < k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 4 < k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (4 ≤ k) ↔ (4 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (4 ≤ k) ↔ (4 < k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (4 ≤ k) ↔ (4 < k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (4 ≤ k) ↔ (4 < k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (4 ≤ k) ↔ (4 < k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (4 ≤ k) ↔ (4 < k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (4 ≤ k) ↔ (4 < k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (4 < k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (4 < k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (4 < k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (4 < k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (4 < k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (4 < k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (4 < k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 5 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 5 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 5 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 5 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 5 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 5 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 5 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 5 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (4 ≤ k) ↔ (5 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (4 ≤ k) ↔ (5 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (4 ≤ k) ↔ (5 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (4 ≤ k) ↔ (5 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (4 ≤ k) ↔ (5 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (4 ≤ k) ↔ (5 ≤ k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (4 ≤ k) ↔ (5 ≤ k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (5 ≤ k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (5 ≤ k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (5 ≤ k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (5 ≤ k)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (5 ≤ k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (5 ≤ k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (5 ≤ k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (5 ≤ k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 4) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (4 ≤ k) ↔ (k ≥ 4) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (4 ≤ k) ↔ (k ≥ 4) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (4 ≤ k) ↔ (k ≥ 4) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (4 ≤ k) ↔ (k ≥ 4) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (4 ≤ k) ↔ (k ≥ 4) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (4 ≤ k) ↔ (k ≥ 4) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (4 ≤ k) ↔ (k ≥ 4) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (4 ≤ k) ↔ (k ≥ 4) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) ↔
    (∀ (k : ℕ) (hk : k ≥ 4) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) ↔
    (∀ (k : ℕ) (hk : k ≥ 4) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) ↔
    (∀ (k : ℕ) (hk : k ≥ 4) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) ↔
    (∀ (k : ℕ) (hk : k ≥ 4) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk' : k ≤ 20) (hk : 4 ≤ k) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) ↔
    (∀ (k : ℕ) (hk' : k ≤ 20) (hk : 4 ≤ k) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) ↔
    (∀ (k : ℕ) (hk' : k ≤ 20) (hk : 4 ≤ k) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) ↔
    (∀ (k : ℕ) (hk' : k ≤ 20) (hk : 4 ≤ k) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) ↔
    (∀ (k : ℕ) (hk' : k ≤ 20) (hk : 4 ≤ k) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk₀ : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) ↔
    (∀ (k : ℕ) (hk₀ : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) ↔
    (∀ (k : ℕ) (hk₀ : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) ↔
    (∀ (k : ℕ) (hk₀ : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) ↔
    (∀ (k : ℕ) (hk₀ : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : ¬(k < 4)) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (4 ≤ k) ↔ (¬(k < 4)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (4 ≤ k) ↔ (¬(k < 4)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (4 ≤ k) ↔ (¬(k < 4)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (4 ≤ k) ↔ (¬(k < 4)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (4 ≤ k) ↔ (¬(k < 4)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (4 ≤ k) ↔ (¬(k < 4)) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (4 ≤ k) ↔ (¬(k < 4)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (4 ≤ k) ↔ (¬(k < 4)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) ↔
    (∀ (k : ℕ) (hk : ¬(k < 4)) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) ↔
    (∀ (k : ℕ) (hk : ¬(k < 4)) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) ↔
    (∀ (k : ℕ) (hk : ¬(k < 4)) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) ↔
    (∀ (k : ℕ) (hk : ¬(k < 4)) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 < k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (4 ≤ k) ↔ (3 < k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (4 ≤ k) ↔ (3 < k) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (4 ≤ k) ↔ (3 < k) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (4 ≤ k) ↔ (3 < k) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (4 ≤ k) ↔ (3 < k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (4 ≤ k) ↔ (3 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (4 ≤ k) ↔ (3 < k) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) :
    (4 ≤ k) ↔ (3 < k) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) ↔
    (∀ (k : ℕ) (hk : 3 < k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) ↔
    (∀ (k : ℕ) (hk : 3 < k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) ↔
    (∀ (k : ℕ) (hk : 3 < k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) ↔
    (∀ (k : ℕ) (hk : 3 < k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k > 4) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : k > 4) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : k > 4) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : k > 4) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : k > 4) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : k > 4) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : k > 4) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : k > 4) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (4 ≤ k) ↔ (k > 4) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (4 ≤ k) ↔ (k > 4) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (4 ≤ k) ↔ (k > 4) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (4 ≤ k) ↔ (k > 4) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (4 ≤ k) ↔ (k > 4) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (4 ≤ k) ↔ (k > 4) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (4 ≤ k) ↔ (k > 4) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (k > 4)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (k > 4)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (k > 4)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (k > 4)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (k > 4)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (k > 4)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (k > 4)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 5) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : k ≥ 5) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : k ≥ 5) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : k ≥ 5) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : k ≥ 5) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : k ≥ 5) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : k ≥ 5) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : k ≥ 5) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (4 ≤ k) ↔ (k ≥ 5) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (4 ≤ k) ↔ (k ≥ 5) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (4 ≤ k) ↔ (k ≥ 5) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (4 ≤ k) ↔ (k ≥ 5) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (4 ≤ k) ↔ (k ≥ 5) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (4 ≤ k) ↔ (k ≥ 5) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (4 ≤ k) ↔ (k ≥ 5) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (k ≥ 5)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (k ≥ 5)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (k ≥ 5)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (k ≥ 5)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (k ≥ 5)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (k ≥ 5)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (k ≥ 5)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (k ≥ 5)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (4 ≤ k) ↔ (3 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (4 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (4 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (4 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (4 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (4 ≤ k) ↔ (3 ≤ k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (4 ≤ k) ↔ (3 ≤ k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 < k) (hk' : k < 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 3 < k) (hk' : k < 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 3 < k) (hk' : k < 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 3 < k) (hk' : k < 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 3 < k) (hk' : k < 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 3 < k) (hk' : k < 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 3 < k) (hk' : k < 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 3 < k) (hk' : k < 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 4 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 20) ↔ (k < 20) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 4 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 20) ↔ (k < 20) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 4 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 20) ↔ (k < 20) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 4 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 20) ↔ (k < 20) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 4 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 20) ↔ (k < 20) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 4 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 20) ↔ (k < 20) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 4 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 20) ↔ (k < 20) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 20) ↔ (k < 20)) :=
  ⟨(20 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 20) ↔ (k < 20)) :=
  ⟨(19 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 20) ↔ (k < 20)) :=
  ⟨(21 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 20) ↔ (k < 20)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 20) ↔ (k < 20)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 20) ↔ (k < 20)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 20) ↔ (k < 20)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 20) ↔ (k < 20)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 20) ↔ (k < 20)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 < k) (hk' : k ≤ 21) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 < k) (hk' : k ≤ 21) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 < k) (hk' : k ≤ 21) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 < k) (hk' : k ≤ 21) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 < k) (hk' : k ≤ 21) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 < k) (hk' : k ≤ 21) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 < k) (hk' : k ≤ 21) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 < k) (hk' : k ≤ 21) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 4 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 20) ↔ (k ≤ 21) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 4 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 20) ↔ (k ≤ 21) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 4 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 20) ↔ (k ≤ 21) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 4 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 20) ↔ (k ≤ 21) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 4 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 20) ↔ (k ≤ 21) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 4 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 20) ↔ (k ≤ 21) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 4 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 20) ↔ (k ≤ 21) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 20) ↔ (k ≤ 21)) :=
  ⟨(20 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 20) ↔ (k ≤ 21)) :=
  ⟨(19 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 20) ↔ (k ≤ 21)) :=
  ⟨(21 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 20) ↔ (k ≤ 21)) :=
  ⟨(22 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 20) ↔ (k ≤ 21)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 20) ↔ (k ≤ 21)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 20) ↔ (k ≤ 21)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 20) ↔ (k ≤ 21)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 20) ↔ (k ≤ 21)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 20) ↔ (k ≤ 21)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (hk' : k ≤ 20) (d : ℕ → ℝ) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)), ¬ IsUnimodalOnPrimes d) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 4 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 20) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 4 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 20) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 4 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 20) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 4 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 20) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 4 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 20) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 4 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 20) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 4 ≤ k) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    (k ≤ 20) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 20) ↔ (True)) :=
  ⟨(20 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 20) ↔ (True)) :=
  ⟨(19 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 20) ↔ (True)) :=
  ⟨(21 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 20) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 20) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 20) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 20) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 20) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 20) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 4 ≤ k) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 4 ≤ k) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 4 ≤ k) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 4 ≤ k) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (d : ℕ → ℝ) (hk : 4 ≤ k) (hk' : k ≤ 20) (hd : ∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
