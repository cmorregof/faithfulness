import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 700

*Reference:* [erdosproblems.com/700](https://www.erdosproblems.com/700)

A problem of Erdős and Szekeres [ErSz78].

*References:*
 * [ErSz78] Erdős, P. and Szekeres, G., _Some number theoretic problems on binomial coefficients_,
   Austral. Math. Soc. Gaz. (1978), 97-99.
 * [OEIS A091963](https://oeis.org/A091963)
 * Guy, R. K., _Unsolved Problems in Number Theory_, B31, B33.
-/

section

namespace Erdos700

open Finset

/-- `f n = min_{1 < k ≤ n/2} gcd(n, C(n,k))`. (The infimum is `0` when the range is empty, i.e.
`n < 4`.) -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {m | ∃ k, 1 < k ∧ k ≤ n / 2 ∧ m = Nat.gcd n (n.choose k)}

/-- `P n` is the largest prime factor of `n` (and `0` if `n ≤ 1`). -/
noncomputable def P (n : ℕ) : ℕ := n.primeFactors.sup id

/-- $Q(n)$ is the largest prime-power divisor of $n$: the maximum of $p^{v_p(n)}$ over
prime divisors $p$ of $n$. It is `0` when `n ≤ 1`. -/
noncomputable def Q (n : ℕ) : ℕ := n.primeFactors.sup (fun p => p ^ n.factorization p)

/-- The set whose infimum defines `f`. -/
def fSet (n : ℕ) : Set ℕ := {m | ∃ k, 1 < k ∧ k ≤ n / 2 ∧ m = Nat.gcd n (n.choose k)}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h2 : k ≤ n / 2) :
    (1 < k) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h2 : k ≤ n / 2) :
    (1 < k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h2 : k ≤ n / 2) :
    (1 < k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h2 : k ≤ n / 2) :
    (1 < k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h2 : k ≤ n / 2) :
    (1 < k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h2 : k ≤ n / 2) :
    (1 < k) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h2 : k ≤ n / 2) :
    (1 < k) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (True))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (h1 : 1 ≤ k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 ≤ k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 ≤ k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 ≤ k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 ≤ k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 ≤ k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 ≤ k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 ≤ k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h2 : k ≤ n / 2) :
    (1 < k) ↔ (1 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h2 : k ≤ n / 2) :
    (1 < k) ↔ (1 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h2 : k ≤ n / 2) :
    (1 < k) ↔ (1 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h2 : k ≤ n / 2) :
    (1 < k) ↔ (1 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h2 : k ≤ n / 2) :
    (1 < k) ↔ (1 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h2 : k ≤ n / 2) :
    (1 < k) ↔ (1 ≤ k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h2 : k ≤ n / 2) :
    (1 < k) ↔ (1 ≤ k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (1 ≤ k))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (1 ≤ k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (1 ≤ k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (1 ≤ k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (1 ≤ k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (1 ≤ k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (1 ≤ k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (h1 : 1 < k) (h2 : k < n / 2), Nat.gcd n (n.choose k) ∈ fSet n

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k < n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k < n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k < n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k < n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k < n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k < n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k < n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h1 : 1 < k) :
    (k ≤ n / 2) ↔ (k < n / 2) := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h1 : 1 < k) :
    (k ≤ n / 2) ↔ (k < n / 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h1 : 1 < k) :
    (k ≤ n / 2) ↔ (k < n / 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h1 : 1 < k) :
    (k ≤ n / 2) ↔ (k < n / 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h1 : 1 < k) :
    (k ≤ n / 2) ↔ (k < n / 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h1 : 1 < k) :
    (k ≤ n / 2) ↔ (k < n / 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h1 : 1 < k) :
    (k ≤ n / 2) ↔ (k < n / 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 3), Nat.gcd n (n.choose k) ∈ fSet n

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 3), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 3), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 3), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 3), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 3), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 3), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 3), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 3), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 3), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 3), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 3), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 3), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 3), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 3), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h1 : 1 < k) :
    (k ≤ n / 2) ↔ (k ≤ n / 3) := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h1 : 1 < k) :
    (k ≤ n / 2) ↔ (k ≤ n / 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h1 : 1 < k) :
    (k ≤ n / 2) ↔ (k ≤ n / 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h1 : 1 < k) :
    (k ≤ n / 2) ↔ (k ≤ n / 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h1 : 1 < k) :
    (k ≤ n / 2) ↔ (k ≤ n / 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h1 : 1 < k) :
    (k ≤ n / 2) ↔ (k ≤ n / 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h1 : 1 < k) :
    (k ≤ n / 2) ↔ (k ≤ n / 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (h1 : k > 1) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (k > 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (k > 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (k > 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (k > 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (k > 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (k > 1) := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (k > 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (k > 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) ↔
    (∀ (n k : ℕ) (h1 : k > 1) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) ↔
    (∀ (n k : ℕ) (h1 : k > 1) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) ↔
    (∀ (n k : ℕ) (h1 : k > 1) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) ↔
    (∀ (n k : ℕ) (h1 : k > 1) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (h2 : k ≤ n / 2) (h1 : 1 < k), Nat.gcd n (n.choose k) ∈ fSet n

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) ↔
    (∀ (n k : ℕ) (h2 : k ≤ n / 2) (h1 : 1 < k), Nat.gcd n (n.choose k) ∈ fSet n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) ↔
    (∀ (n k : ℕ) (h2 : k ≤ n / 2) (h1 : 1 < k), Nat.gcd n (n.choose k) ∈ fSet n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) ↔
    (∀ (n k : ℕ) (h2 : k ≤ n / 2) (h1 : 1 < k), Nat.gcd n (n.choose k) ∈ fSet n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) ↔
    (∀ (n k : ℕ) (h2 : k ≤ n / 2) (h1 : 1 < k), Nat.gcd n (n.choose k) ∈ fSet n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (h1' : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) ↔
    (∀ (n k : ℕ) (h1' : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) ↔
    (∀ (n k : ℕ) (h1' : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) ↔
    (∀ (n k : ℕ) (h1' : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) ↔
    (∀ (n k : ℕ) (h1' : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (h1 : ¬(k ≤ 1)) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (¬(k ≤ 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (¬(k ≤ 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (¬(k ≤ 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (¬(k ≤ 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (¬(k ≤ 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (¬(k ≤ 1)) := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (¬(k ≤ 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (¬(k ≤ 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) ↔
    (∀ (n k : ℕ) (h1 : ¬(k ≤ 1)) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) ↔
    (∀ (n k : ℕ) (h1 : ¬(k ≤ 1)) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) ↔
    (∀ (n k : ℕ) (h1 : ¬(k ≤ 1)) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) ↔
    (∀ (n k : ℕ) (h1 : ¬(k ≤ 1)) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (h1 : 2 ≤ k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (2 ≤ k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (2 ≤ k) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (2 ≤ k) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (2 ≤ k) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (2 ≤ k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (2 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (2 ≤ k) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 < k) ↔ (2 ≤ k) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) ↔
    (∀ (n k : ℕ) (h1 : 2 ≤ k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) ↔
    (∀ (n k : ℕ) (h1 : 2 ≤ k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) ↔
    (∀ (n k : ℕ) (h1 : 2 ≤ k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) ↔
    (∀ (n k : ℕ) (h1 : 2 ≤ k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (h1 : k ≥ 1) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : k ≥ 1) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : k ≥ 1) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : k ≥ 1) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : k ≥ 1) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : k ≥ 1) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : k ≥ 1) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : k ≥ 1) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h2 : k ≤ n / 2) :
    (1 < k) ↔ (k ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h2 : k ≤ n / 2) :
    (1 < k) ↔ (k ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h2 : k ≤ n / 2) :
    (1 < k) ↔ (k ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h2 : k ≤ n / 2) :
    (1 < k) ↔ (k ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h2 : k ≤ n / 2) :
    (1 < k) ↔ (k ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h2 : k ≤ n / 2) :
    (1 < k) ↔ (k ≥ 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h2 : k ≤ n / 2) :
    (1 < k) ↔ (k ≥ 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (k ≥ 1))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (k ≥ 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (k ≥ 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (k ≥ 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (k ≥ 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (k ≥ 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (k ≥ 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (h1 : k > 1) (h2 : k < n / 2), Nat.gcd n (n.choose k) ∈ fSet n

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : k > 1) (h2 : k < n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : k > 1) (h2 : k < n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : k > 1) (h2 : k < n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : k > 1) (h2 : k < n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : k > 1) (h2 : k < n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : k > 1) (h2 : k < n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : k > 1) (h2 : k < n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h1 : 1 < k) :
    (k ≤ n / 2) ↔ (k < n / 2) := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h1 : 1 < k) :
    (k ≤ n / 2) ↔ (k < n / 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h1 : 1 < k) :
    (k ≤ n / 2) ↔ (k < n / 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h1 : 1 < k) :
    (k ≤ n / 2) ↔ (k < n / 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h1 : 1 < k) :
    (k ≤ n / 2) ↔ (k < n / 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h1 : 1 < k) :
    (k ≤ n / 2) ↔ (k < n / 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h1 : 1 < k) :
    (k ≤ n / 2) ↔ (k < n / 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k < n / 2))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k < n / 2)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (h1 : k > 1) (h2 : k ≤ n / 3), Nat.gcd n (n.choose k) ∈ fSet n

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : k > 1) (h2 : k ≤ n / 3), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : k > 1) (h2 : k ≤ n / 3), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : k > 1) (h2 : k ≤ n / 3), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : k > 1) (h2 : k ≤ n / 3), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : k > 1) (h2 : k ≤ n / 3), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : k > 1) (h2 : k ≤ n / 3), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : k > 1) (h2 : k ≤ n / 3), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : k > 1) (h2 : k ≤ n / 3), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : k > 1) (h2 : k ≤ n / 3), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : k > 1) (h2 : k ≤ n / 3), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : k > 1) (h2 : k ≤ n / 3), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : k > 1) (h2 : k ≤ n / 3), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : k > 1) (h2 : k ≤ n / 3), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : k > 1) (h2 : k ≤ n / 3), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h1 : 1 < k) :
    (k ≤ n / 2) ↔ (k ≤ n / 3) := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h1 : 1 < k) :
    (k ≤ n / 2) ↔ (k ≤ n / 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h1 : 1 < k) :
    (k ≤ n / 2) ↔ (k ≤ n / 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h1 : 1 < k) :
    (k ≤ n / 2) ↔ (k ≤ n / 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h1 : 1 < k) :
    (k ≤ n / 2) ↔ (k ≤ n / 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h1 : 1 < k) :
    (k ≤ n / 2) ↔ (k ≤ n / 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h1 : 1 < k) :
    (k ≤ n / 2) ↔ (k ≤ n / 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (k ≤ n / 3))) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (k ≤ n / 3)) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (h1 : 2 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 2 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 2 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 2 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 2 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 2 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 2 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 2 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h2 : k ≤ n / 2) :
    (1 < k) ↔ (2 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h2 : k ≤ n / 2) :
    (1 < k) ↔ (2 < k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h2 : k ≤ n / 2) :
    (1 < k) ↔ (2 < k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h2 : k ≤ n / 2) :
    (1 < k) ↔ (2 < k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h2 : k ≤ n / 2) :
    (1 < k) ↔ (2 < k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h2 : k ≤ n / 2) :
    (1 < k) ↔ (2 < k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h2 : k ≤ n / 2) :
    (1 < k) ↔ (2 < k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (2 < k))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (2 < k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (2 < k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (2 < k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (2 < k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (2 < k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (2 < k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (h1 : 3 ≤ k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 3 ≤ k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 3 ≤ k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 3 ≤ k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 3 ≤ k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 3 ≤ k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 3 ≤ k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 3 ≤ k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h2 : k ≤ n / 2) :
    (1 < k) ↔ (3 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h2 : k ≤ n / 2) :
    (1 < k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h2 : k ≤ n / 2) :
    (1 < k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h2 : k ≤ n / 2) :
    (1 < k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h2 : k ≤ n / 2) :
    (1 < k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h2 : k ≤ n / 2) :
    (1 < k) ↔ (3 ≤ k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h2 : k ≤ n / 2) :
    (1 < k) ↔ (3 ≤ k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n / 2) ∧ (¬((1 < k) ↔ (3 ≤ k))) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (3 ≤ k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (3 ≤ k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (3 ≤ k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (3 ≤ k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (3 ≤ k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (3 ≤ k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 < k) ↔ (3 ≤ k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (h1 : 1 < k), Nat.gcd n (n.choose k) ∈ fSet n

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (h1 : 1 < k), Nat.gcd n (n.choose k) ∈ fSet n) →
    (∀ (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2), Nat.gcd n (n.choose k) ∈ fSet n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h1 : 1 < k) :
    (k ≤ n / 2) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h1 : 1 < k) :
    (k ≤ n / 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h1 : 1 < k) :
    (k ≤ n / 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h1 : 1 < k) :
    (k ≤ n / 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h1 : 1 < k) :
    (k ≤ n / 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h1 : 1 < k) :
    (k ≤ n / 2) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h1 : 1 < k) :
    (k ≤ n / 2) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (True))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (True))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (True))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (True))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (True))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (True))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (True))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (True))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (True))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (True))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (True))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (True))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (True))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (True))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (True))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (True))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (True))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (True))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 < k) ∧ (¬((k ≤ n / 2) ↔ (True))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (True)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (True)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (True)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (True)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (True)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (True)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (True)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (True)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (True)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (True)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (True)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (True)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (True)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (True)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (True)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (True)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (True)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (True)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (True)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (True)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (True)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (True)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (True)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (True)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (True)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (True)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (True)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (True)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (True)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (True)) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (True)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n / 2) ↔ (True)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
