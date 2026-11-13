import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 860

*References:*
- [erdosproblems.com/860](https://www.erdosproblems.com/860)
- [ErPo80] Erdős, P. and Pomerance, C., *Matching the natural numbers up to $n$ with distinct
  multiples in another interval*. Nederl. Akad. Wetensch. Indag. Math. 42 (1980), 147-161.
  [PDF](https://www.renyi.hu/~p_erdos/1980-13.pdf)
- [Er92c] Erdős, P., *Some of my forgotten problems in number theory*. Hardy-Ramanujan J. 15
  (1992), 34-50. [PDF](https://hrj.episciences.org/125/pdf)
-/

section

open Filter Asymptotics

namespace Erdos860

/-- There are distinct integers $a_1,\ldots,a_{\pi(n)}$ in the open interval $(m,m+L)$ such that
$p_i \mid a_i$ for every $1 \leq i \leq \pi(n)$, where $p_i$ is the $i$th prime. Primes are
indexed from $0$ by `Nat.nth Nat.Prime`, so $p_i$ is `Nat.nth Nat.Prime (i - 1)`. -/
def HasPrimeMultiples (n m L : ℕ) : Prop :=
  ∃ a : Fin (Nat.primeCounting n) → ℕ,
    Function.Injective a ∧ ∀ i, m < a i ∧ a i < m + L ∧ Nat.nth Nat.Prime i.val ∣ a i

/-- $h(n)$: the least $L$ such that for every $m \geq 1$ the open interval $(m,m+L)$ contains
distinct integers $a_1,\ldots,a_{\pi(n)}$ with $p_i \mid a_i$, where $p_i$ is the $i$th prime.

The set of such $L$ is nonempty: $L = n\pi(n)+1$ works, since each $p_i \leq n$ has at least
$\pi(n)$ multiples in $(m,m+L)$, so the $a_i$ can be chosen one by one. So `sInf` is the true
minimum. For $n < 2$ there are no primes and $h(n) = 0$. -/
noncomputable def h (n : ℕ) : ℕ :=
  sInf {L : ℕ | ∀ m, 1 ≤ m → HasPrimeMultiples n m L}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n < L

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n < L) →
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n < L) →
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n < L) →
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n < L) →
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n < L) →
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n < L) →
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n < L) →
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n < L)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n < L)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n < L)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n < L)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n < L)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n < L)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n < L)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n < L)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n < L)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n < L)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n < L)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n < L)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n < L)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n < L)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n < L)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n < L)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n < L)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n < L)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n < L)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n < L)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n < L)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n < L)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n < L)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n < L)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n < L)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n < L)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n < L)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n < L)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n < L)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n < L)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n < L)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n < L)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n < L)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n < L)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n < L)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n < L)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n < L)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n < L)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n < L)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n < L)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n < L)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n < L)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n < L)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n < L)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n < L)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n < L)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n < L)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n < L)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n < L)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n < L)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n < L)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n < L)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n < L)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n < L)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n < L)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n < L)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n < L)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n < L)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n < L)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n < L)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n < L)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n < L)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n < L)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n < L)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≥ L

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≥ L) →
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≥ L) →
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≥ L) →
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≥ L) →
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≥ L) →
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≥ L) →
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≥ L) →
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) →
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≥ L) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) →
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≥ L) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) →
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≥ L) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) →
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≥ L) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) →
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≥ L) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) →
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≥ L) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) →
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≥ L) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n ≥ L)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n ≥ L)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n ≥ L)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n ≥ L)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n ≥ L)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n ≥ L)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n ≥ L)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n ≥ L)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n ≥ L)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n ≥ L)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n ≥ L)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n ≥ L)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n ≥ L)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n ≥ L)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n ≥ L)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n ≥ L)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n ≥ L)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n ≥ L)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n ≥ L)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n ≥ L)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n ≥ L)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n ≥ L)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n ≥ L)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n ≥ L)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n ≥ L)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n ≥ L)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n ≥ L)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n ≥ L)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n ≥ L)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n ≥ L)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n ≥ L)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(h n ≥ L)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n ≥ L)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n ≥ L)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n ≥ L)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n ≥ L)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n ≥ L)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n ≥ L)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n ≥ L)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n ≥ L)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n ≥ L)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n ≥ L)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n ≥ L)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n ≥ L)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n ≥ L)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n ≥ L)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n ≥ L)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n ≥ L)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n ≥ L)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n ≥ L)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n ≥ L)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n ≥ L)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n ≥ L)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n ≥ L)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n ≥ L)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n ≥ L)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n ≥ L)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n ≥ L)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n ≥ L)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n ≥ L)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n ≥ L)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n ≥ L)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n ≥ L)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (h n ≥ L)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), L ≥ h n

set_option maxHeartbeats 200000 in
example {n L : ℕ} :
    (h n ≤ L) ↔ (L ≥ h n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n L : ℕ} :
    (h n ≤ L) ↔ (L ≥ h n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n L : ℕ} :
    (h n ≤ L) ↔ (L ≥ h n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n L : ℕ} :
    (h n ≤ L) ↔ (L ≥ h n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n L : ℕ} :
    (h n ≤ L) ↔ (L ≥ h n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n L : ℕ} :
    (h n ≤ L) ↔ (L ≥ h n) := by
  omega

set_option maxHeartbeats 200000 in
example {n L : ℕ} :
    (h n ≤ L) ↔ (L ≥ h n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n L : ℕ} :
    (h n ≤ L) ↔ (L ≥ h n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) ↔
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), L ≥ h n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) ↔
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), L ≥ h n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) ↔
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), L ≥ h n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) ↔
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), L ≥ h n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n L : ℕ} (hL₀ : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) ↔
    (∀ {n L : ℕ} (hL₀ : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) ↔
    (∀ {n L : ℕ} (hL₀ : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) ↔
    (∀ {n L : ℕ} (hL₀ : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) ↔
    (∀ {n L : ℕ} (hL₀ : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), ¬(L < h n)

set_option maxHeartbeats 200000 in
example {n L : ℕ} :
    (h n ≤ L) ↔ (¬(L < h n)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n L : ℕ} :
    (h n ≤ L) ↔ (¬(L < h n)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n L : ℕ} :
    (h n ≤ L) ↔ (¬(L < h n)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n L : ℕ} :
    (h n ≤ L) ↔ (¬(L < h n)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n L : ℕ} :
    (h n ≤ L) ↔ (¬(L < h n)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n L : ℕ} :
    (h n ≤ L) ↔ (¬(L < h n)) := by
  omega

set_option maxHeartbeats 200000 in
example {n L : ℕ} :
    (h n ≤ L) ↔ (¬(L < h n)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n L : ℕ} :
    (h n ≤ L) ↔ (¬(L < h n)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) ↔
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), ¬(L < h n)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) ↔
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), ¬(L < h n)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) ↔
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), ¬(L < h n)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) ↔
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), ¬(L < h n)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), L > h n

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), L > h n) →
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), L > h n) →
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), L > h n) →
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), L > h n) →
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), L > h n) →
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), L > h n) →
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), L > h n) →
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L > h n)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L > h n)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L > h n)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L > h n)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L > h n)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L > h n)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L > h n)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L > h n)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L > h n)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L > h n)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L > h n)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L > h n)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L > h n)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L > h n)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L > h n)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L > h n)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L > h n)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L > h n)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L > h n)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L > h n)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L > h n)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L > h n)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L > h n)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L > h n)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L > h n)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L > h n)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L > h n)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L > h n)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L > h n)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L > h n)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L > h n)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L > h n)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L > h n)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L > h n)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L > h n)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L > h n)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L > h n)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L > h n)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L > h n)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L > h n)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L > h n)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L > h n)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L > h n)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L > h n)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L > h n)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L > h n)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L > h n)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L > h n)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L > h n)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L > h n)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L > h n)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L > h n)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L > h n)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L > h n)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L > h n)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L > h n)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L > h n)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L > h n)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L > h n)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L > h n)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L > h n)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L > h n)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L > h n)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L > h n)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), L ≤ h n

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), L ≤ h n) →
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), L ≤ h n) →
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), L ≤ h n) →
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), L ≤ h n) →
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), L ≤ h n) →
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), L ≤ h n) →
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), L ≤ h n) →
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) →
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), L ≤ h n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) →
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), L ≤ h n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) →
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), L ≤ h n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) →
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), L ≤ h n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) →
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), L ≤ h n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) →
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), L ≤ h n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), h n ≤ L) →
    (∀ {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L), L ≤ h n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L ≤ h n)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L ≤ h n)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L ≤ h n)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L ≤ h n)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L ≤ h n)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L ≤ h n)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L ≤ h n)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L ≤ h n)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L ≤ h n)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L ≤ h n)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L ≤ h n)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L ≤ h n)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L ≤ h n)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L ≤ h n)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L ≤ h n)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L ≤ h n)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L ≤ h n)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L ≤ h n)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L ≤ h n)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L ≤ h n)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L ≤ h n)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L ≤ h n)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L ≤ h n)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L ≤ h n)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L ≤ h n)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L ≤ h n)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L ≤ h n)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L ≤ h n)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L ≤ h n)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L ≤ h n)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L ≤ h n)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), (∀ m, 1 ≤ m → HasPrimeMultiples n m L) ∧ (¬(L ≤ h n)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L ≤ h n)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L ≤ h n)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L ≤ h n)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L ≤ h n)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L ≤ h n)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L ≤ h n)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L ≤ h n)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L ≤ h n)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L ≤ h n)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L ≤ h n)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L ≤ h n)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L ≤ h n)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L ≤ h n)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L ≤ h n)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L ≤ h n)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L ≤ h n)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L ≤ h n)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L ≤ h n)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L ≤ h n)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L ≤ h n)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L ≤ h n)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L ≤ h n)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L ≤ h n)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L ≤ h n)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L ≤ h n)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L ≤ h n)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L ≤ h n)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L ≤ h n)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L ≤ h n)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L ≤ h n)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L ≤ h n)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (L : ℕ), ¬((h n ≤ L) ↔ (L ≤ h n)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {n L : ℕ} (hL : ∀ m, 1 ≤ m → HasPrimeMultiples n m L) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
