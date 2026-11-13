import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Factor bounds for Fermat numbers

$a(n)$ is the minimum integer $k$ such that the smallest prime factor of the
$n$-th Fermat number exceeds $2^{2^n - k}$.

*References:*
- [A358684](https://oeis.org/A358684)
- [SA22](https://doi.org/10.26493/2590-9770.1473.ec5) Lorenzo Sauras-Altuzarra, *Some properties of the factors of Fermat numbers*, Art Discrete Appl. Math. (2022).
-/

section

namespace OeisA358684

open Nat

/--
A358684: $a(n)$ is the minimum integer $k$ such that the smallest prime factor of the $n$-th Fermat
number exceeds $2^{2^n - k}$.
Let $F_n = 2^{2^n} + 1$ be the $n$-th Fermat number, and $P_n$ be its smallest prime factor.
The definition of $a(n)$ is equivalent to the closed form:
$$a(n) = 2^n - \lfloor \log_2(P_n) \rfloor$$
where $P_n = \operatorname{minFac}(\operatorname{fermatNumber} n)$.
The subtraction is defined in $\mathbb{N}$ and is safe
 since $P_n \le F_n$, implying $\log_2 P_n < 2^n$.
-/
def a (n : ℕ) : ℕ :=
  letI pn := minFac (fermatNumber n)
  (2 ^ n) - (log2 pn)

/--
The "original" definition: $a'(n)$ is the minimum $k$ such that $P_n > 2^{2^n - k}$.
We use `Nat.find` which returns the smallest natural number satisfying a predicate.
-/
noncomputable def a' (n : ℕ) : ℕ :=
  letI Pn := minFac (fermatNumber n)
  Nat.find (show ∃ k, Pn > 2 ^ (2 ^ n - k) from by
    use 2^n
    simp only [tsub_self, pow_zero]
    simp [Pn]
    unfold Nat.fermatNumber
    exact (Nat.minFac_prime (by norm_num)).one_lt
  )

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) < 2 ^ n - a n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) < 2 ^ n - a n) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) < 2 ^ n - a n) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) < 2 ^ n - a n) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) < 2 ^ n - a n) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) < 2 ^ n - a n) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) < 2 ^ n - a n) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) < 2 ^ n - a n) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(padicValNat 2 (minFac (fermatNumber n) - 1) < 2 ^ n - a n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(padicValNat 2 (minFac (fermatNumber n) - 1) < 2 ^ n - a n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(padicValNat 2 (minFac (fermatNumber n) - 1) < 2 ^ n - a n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(padicValNat 2 (minFac (fermatNumber n) - 1) < 2 ^ n - a n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(padicValNat 2 (minFac (fermatNumber n) - 1) < 2 ^ n - a n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(padicValNat 2 (minFac (fermatNumber n) - 1) < 2 ^ n - a n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (padicValNat 2 (minFac (fermatNumber n) - 1) < 2 ^ n - a n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (padicValNat 2 (minFac (fermatNumber n) - 1) < 2 ^ n - a n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (padicValNat 2 (minFac (fermatNumber n) - 1) < 2 ^ n - a n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (padicValNat 2 (minFac (fermatNumber n) - 1) < 2 ^ n - a n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (padicValNat 2 (minFac (fermatNumber n) - 1) < 2 ^ n - a n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (padicValNat 2 (minFac (fermatNumber n) - 1) < 2 ^ n - a n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), padicValNat 3 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 3 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 3 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 3 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 3 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 3 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 3 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 3 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) →
    (∀ (n : ℕ), padicValNat 3 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) →
    (∀ (n : ℕ), padicValNat 3 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) →
    (∀ (n : ℕ), padicValNat 3 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) →
    (∀ (n : ℕ), padicValNat 3 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) →
    (∀ (n : ℕ), padicValNat 3 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) →
    (∀ (n : ℕ), padicValNat 3 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) →
    (∀ (n : ℕ), padicValNat 3 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(padicValNat 3 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(padicValNat 3 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(padicValNat 3 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(padicValNat 3 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(padicValNat 3 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(padicValNat 3 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(padicValNat 3 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (padicValNat 3 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (padicValNat 3 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (padicValNat 3 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (padicValNat 3 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (padicValNat 3 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (padicValNat 3 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (padicValNat 3 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≥ 2 ^ n - a n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≥ 2 ^ n - a n) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≥ 2 ^ n - a n) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≥ 2 ^ n - a n) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≥ 2 ^ n - a n) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≥ 2 ^ n - a n) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≥ 2 ^ n - a n) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≥ 2 ^ n - a n) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≥ 2 ^ n - a n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≥ 2 ^ n - a n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≥ 2 ^ n - a n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≥ 2 ^ n - a n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≥ 2 ^ n - a n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≥ 2 ^ n - a n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≥ 2 ^ n - a n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(padicValNat 2 (minFac (fermatNumber n) - 1) ≥ 2 ^ n - a n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(padicValNat 2 (minFac (fermatNumber n) - 1) ≥ 2 ^ n - a n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(padicValNat 2 (minFac (fermatNumber n) - 1) ≥ 2 ^ n - a n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(padicValNat 2 (minFac (fermatNumber n) - 1) ≥ 2 ^ n - a n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(padicValNat 2 (minFac (fermatNumber n) - 1) ≥ 2 ^ n - a n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(padicValNat 2 (minFac (fermatNumber n) - 1) ≥ 2 ^ n - a n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (padicValNat 2 (minFac (fermatNumber n) - 1) ≥ 2 ^ n - a n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (padicValNat 2 (minFac (fermatNumber n) - 1) ≥ 2 ^ n - a n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (padicValNat 2 (minFac (fermatNumber n) - 1) ≥ 2 ^ n - a n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (padicValNat 2 (minFac (fermatNumber n) - 1) ≥ 2 ^ n - a n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (padicValNat 2 (minFac (fermatNumber n) - 1) ≥ 2 ^ n - a n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (padicValNat 2 (minFac (fermatNumber n) - 1) ≥ 2 ^ n - a n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), 2 ^ n - a n ≥ padicValNat 2 (minFac (fermatNumber n) - 1)

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (2 ^ n - a n ≥ padicValNat 2 (minFac (fermatNumber n) - 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (2 ^ n - a n ≥ padicValNat 2 (minFac (fermatNumber n) - 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (2 ^ n - a n ≥ padicValNat 2 (minFac (fermatNumber n) - 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (2 ^ n - a n ≥ padicValNat 2 (minFac (fermatNumber n) - 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (2 ^ n - a n ≥ padicValNat 2 (minFac (fermatNumber n) - 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (2 ^ n - a n ≥ padicValNat 2 (minFac (fermatNumber n) - 1)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (2 ^ n - a n ≥ padicValNat 2 (minFac (fermatNumber n) - 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (2 ^ n - a n ≥ padicValNat 2 (minFac (fermatNumber n) - 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔
    (∀ (n : ℕ), 2 ^ n - a n ≥ padicValNat 2 (minFac (fermatNumber n) - 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔
    (∀ (n : ℕ), 2 ^ n - a n ≥ padicValNat 2 (minFac (fermatNumber n) - 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔
    (∀ (n : ℕ), 2 ^ n - a n ≥ padicValNat 2 (minFac (fermatNumber n) - 1)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔
    (∀ (n : ℕ), 2 ^ n - a n ≥ padicValNat 2 (minFac (fermatNumber n) - 1)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), ¬(2 ^ n - a n < padicValNat 2 (minFac (fermatNumber n) - 1))

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (¬(2 ^ n - a n < padicValNat 2 (minFac (fermatNumber n) - 1))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (¬(2 ^ n - a n < padicValNat 2 (minFac (fermatNumber n) - 1))) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (¬(2 ^ n - a n < padicValNat 2 (minFac (fermatNumber n) - 1))) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (¬(2 ^ n - a n < padicValNat 2 (minFac (fermatNumber n) - 1))) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (¬(2 ^ n - a n < padicValNat 2 (minFac (fermatNumber n) - 1))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (¬(2 ^ n - a n < padicValNat 2 (minFac (fermatNumber n) - 1))) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (¬(2 ^ n - a n < padicValNat 2 (minFac (fermatNumber n) - 1))) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (¬(2 ^ n - a n < padicValNat 2 (minFac (fermatNumber n) - 1))) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔
    (∀ (n : ℕ), ¬(2 ^ n - a n < padicValNat 2 (minFac (fermatNumber n) - 1))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔
    (∀ (n : ℕ), ¬(2 ^ n - a n < padicValNat 2 (minFac (fermatNumber n) - 1))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔
    (∀ (n : ℕ), ¬(2 ^ n - a n < padicValNat 2 (minFac (fermatNumber n) - 1))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔
    (∀ (n : ℕ), ¬(2 ^ n - a n < padicValNat 2 (minFac (fermatNumber n) - 1))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), 2 ^ n - a n > padicValNat 2 (minFac (fermatNumber n) - 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 2 ^ n - a n > padicValNat 2 (minFac (fermatNumber n) - 1)) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 2 ^ n - a n > padicValNat 2 (minFac (fermatNumber n) - 1)) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 2 ^ n - a n > padicValNat 2 (minFac (fermatNumber n) - 1)) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 2 ^ n - a n > padicValNat 2 (minFac (fermatNumber n) - 1)) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 2 ^ n - a n > padicValNat 2 (minFac (fermatNumber n) - 1)) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 2 ^ n - a n > padicValNat 2 (minFac (fermatNumber n) - 1)) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 2 ^ n - a n > padicValNat 2 (minFac (fermatNumber n) - 1)) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(2 ^ n - a n > padicValNat 2 (minFac (fermatNumber n) - 1))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(2 ^ n - a n > padicValNat 2 (minFac (fermatNumber n) - 1))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(2 ^ n - a n > padicValNat 2 (minFac (fermatNumber n) - 1))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(2 ^ n - a n > padicValNat 2 (minFac (fermatNumber n) - 1))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(2 ^ n - a n > padicValNat 2 (minFac (fermatNumber n) - 1))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(2 ^ n - a n > padicValNat 2 (minFac (fermatNumber n) - 1))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (2 ^ n - a n > padicValNat 2 (minFac (fermatNumber n) - 1))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (2 ^ n - a n > padicValNat 2 (minFac (fermatNumber n) - 1))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (2 ^ n - a n > padicValNat 2 (minFac (fermatNumber n) - 1))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (2 ^ n - a n > padicValNat 2 (minFac (fermatNumber n) - 1))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (2 ^ n - a n > padicValNat 2 (minFac (fermatNumber n) - 1))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (2 ^ n - a n > padicValNat 2 (minFac (fermatNumber n) - 1))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), 3 ^ n - a n ≥ padicValNat 2 (minFac (fermatNumber n) - 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 3 ^ n - a n ≥ padicValNat 2 (minFac (fermatNumber n) - 1)) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 3 ^ n - a n ≥ padicValNat 2 (minFac (fermatNumber n) - 1)) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 3 ^ n - a n ≥ padicValNat 2 (minFac (fermatNumber n) - 1)) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 3 ^ n - a n ≥ padicValNat 2 (minFac (fermatNumber n) - 1)) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 3 ^ n - a n ≥ padicValNat 2 (minFac (fermatNumber n) - 1)) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 3 ^ n - a n ≥ padicValNat 2 (minFac (fermatNumber n) - 1)) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 3 ^ n - a n ≥ padicValNat 2 (minFac (fermatNumber n) - 1)) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) →
    (∀ (n : ℕ), 3 ^ n - a n ≥ padicValNat 2 (minFac (fermatNumber n) - 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) →
    (∀ (n : ℕ), 3 ^ n - a n ≥ padicValNat 2 (minFac (fermatNumber n) - 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) →
    (∀ (n : ℕ), 3 ^ n - a n ≥ padicValNat 2 (minFac (fermatNumber n) - 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) →
    (∀ (n : ℕ), 3 ^ n - a n ≥ padicValNat 2 (minFac (fermatNumber n) - 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) →
    (∀ (n : ℕ), 3 ^ n - a n ≥ padicValNat 2 (minFac (fermatNumber n) - 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) →
    (∀ (n : ℕ), 3 ^ n - a n ≥ padicValNat 2 (minFac (fermatNumber n) - 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) →
    (∀ (n : ℕ), 3 ^ n - a n ≥ padicValNat 2 (minFac (fermatNumber n) - 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(3 ^ n - a n ≥ padicValNat 2 (minFac (fermatNumber n) - 1))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(3 ^ n - a n ≥ padicValNat 2 (minFac (fermatNumber n) - 1))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(3 ^ n - a n ≥ padicValNat 2 (minFac (fermatNumber n) - 1))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(3 ^ n - a n ≥ padicValNat 2 (minFac (fermatNumber n) - 1))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(3 ^ n - a n ≥ padicValNat 2 (minFac (fermatNumber n) - 1))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(3 ^ n - a n ≥ padicValNat 2 (minFac (fermatNumber n) - 1))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(3 ^ n - a n ≥ padicValNat 2 (minFac (fermatNumber n) - 1))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (3 ^ n - a n ≥ padicValNat 2 (minFac (fermatNumber n) - 1))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (3 ^ n - a n ≥ padicValNat 2 (minFac (fermatNumber n) - 1))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (3 ^ n - a n ≥ padicValNat 2 (minFac (fermatNumber n) - 1))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (3 ^ n - a n ≥ padicValNat 2 (minFac (fermatNumber n) - 1))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (3 ^ n - a n ≥ padicValNat 2 (minFac (fermatNumber n) - 1))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (3 ^ n - a n ≥ padicValNat 2 (minFac (fermatNumber n) - 1))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (3 ^ n - a n ≥ padicValNat 2 (minFac (fermatNumber n) - 1))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), 2 ^ n - a n ≤ padicValNat 2 (minFac (fermatNumber n) - 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 2 ^ n - a n ≤ padicValNat 2 (minFac (fermatNumber n) - 1)) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 2 ^ n - a n ≤ padicValNat 2 (minFac (fermatNumber n) - 1)) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 2 ^ n - a n ≤ padicValNat 2 (minFac (fermatNumber n) - 1)) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 2 ^ n - a n ≤ padicValNat 2 (minFac (fermatNumber n) - 1)) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 2 ^ n - a n ≤ padicValNat 2 (minFac (fermatNumber n) - 1)) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 2 ^ n - a n ≤ padicValNat 2 (minFac (fermatNumber n) - 1)) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 2 ^ n - a n ≤ padicValNat 2 (minFac (fermatNumber n) - 1)) →
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) →
    (∀ (n : ℕ), 2 ^ n - a n ≤ padicValNat 2 (minFac (fermatNumber n) - 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) →
    (∀ (n : ℕ), 2 ^ n - a n ≤ padicValNat 2 (minFac (fermatNumber n) - 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) →
    (∀ (n : ℕ), 2 ^ n - a n ≤ padicValNat 2 (minFac (fermatNumber n) - 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) →
    (∀ (n : ℕ), 2 ^ n - a n ≤ padicValNat 2 (minFac (fermatNumber n) - 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) →
    (∀ (n : ℕ), 2 ^ n - a n ≤ padicValNat 2 (minFac (fermatNumber n) - 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) →
    (∀ (n : ℕ), 2 ^ n - a n ≤ padicValNat 2 (minFac (fermatNumber n) - 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) →
    (∀ (n : ℕ), 2 ^ n - a n ≤ padicValNat 2 (minFac (fermatNumber n) - 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(2 ^ n - a n ≤ padicValNat 2 (minFac (fermatNumber n) - 1))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(2 ^ n - a n ≤ padicValNat 2 (minFac (fermatNumber n) - 1))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(2 ^ n - a n ≤ padicValNat 2 (minFac (fermatNumber n) - 1))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(2 ^ n - a n ≤ padicValNat 2 (minFac (fermatNumber n) - 1))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(2 ^ n - a n ≤ padicValNat 2 (minFac (fermatNumber n) - 1))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(2 ^ n - a n ≤ padicValNat 2 (minFac (fermatNumber n) - 1))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (2 ^ n - a n ≤ padicValNat 2 (minFac (fermatNumber n) - 1))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (2 ^ n - a n ≤ padicValNat 2 (minFac (fermatNumber n) - 1))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (2 ^ n - a n ≤ padicValNat 2 (minFac (fermatNumber n) - 1))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (2 ^ n - a n ≤ padicValNat 2 (minFac (fermatNumber n) - 1))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (2 ^ n - a n ≤ padicValNat 2 (minFac (fermatNumber n) - 1))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n) ↔ (2 ^ n - a n ≤ padicValNat 2 (minFac (fermatNumber n) - 1))) :=
  ⟨(10 : ℕ), by norm_num⟩

#eval "FIN_CERTIFICAR"
