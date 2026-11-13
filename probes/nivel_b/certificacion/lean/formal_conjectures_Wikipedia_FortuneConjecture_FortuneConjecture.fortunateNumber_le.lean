import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Fortune's Conjecture

A *Fortunate number* is the smallest integer $m > 1$ such that $p_n\\# + m$ is prime,
where $p_n\\#$ denotes the primorial of the $n$-th prime — equivalently, the product
of the first $n$ primes.

**Fortune's Conjecture** asserts that every Fortunate number is prime — equivalently,
that no Fortunate number is composite.

The conjecture is named after the social anthropologist Reo Fortune, who proposed it.
The first few Fortunate numbers are $3, 5, 7, 13, 23, 17, 19, 23, 37, 61, \ldots$
(OEIS A005235); all known values are prime.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Fortunate_number)
- [OEIS A005235](https://oeis.org/A005235)
- [PrimePages glossary entry](https://primes.utm.edu/glossary/xpage/FortunateNumber.html)
- [PlanetMath: Fortune's conjecture](https://planetmath.org/fortunesconjecture)
-/

section

namespace FortuneConjecture

open Nat

/-- For any natural number `N` there is some `m > 1` with `N + m` prime; an
immediate consequence of the infinitude of primes. -/
lemma exists_one_lt_prime_add (N : ℕ) : ∃ m, 1 < m ∧ Nat.Prime (N + m) := by
  obtain ⟨p, hp_ge, hp_prime⟩ := Nat.exists_infinite_primes (N + 2)
  refine ⟨p - N, by omega, ?_⟩
  have hsum : N + (p - N) = p := by omega
  rw [hsum]; exact hp_prime

/-- The $n$-th *Fortunate number* (0-indexed): the smallest integer $m > 1$ such
that $p_{n+1}\\# + m$ is prime.

`Nat.nth Nat.Prime n` is the $(n+1)$-st prime (0-indexed), and `primorial p` is the
product of all primes $\le p$; when $p$ is the $(n+1)$-st prime this equals the
product of the first $n+1$ primes. Thus `fortunateNumber 0` corresponds to
$F_1 = 3$ in the OEIS A005235 indexing. -/
noncomputable def fortunateNumber (n : ℕ) : ℕ :=
  Nat.find (exists_one_lt_prime_add (primorial (Nat.nth Nat.Prime n)))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    (1 < m) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    (1 < m) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    (1 < m) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    (1 < m) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    (1 < m) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    (1 < m) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    (1 < m) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n < m

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n < m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n < m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n < m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n < m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n < m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n < m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n < m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hm : 1 ≤ m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 ≤ m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 ≤ m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 ≤ m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 ≤ m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 ≤ m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 ≤ m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 ≤ m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    (1 < m) ↔ (1 ≤ m) := by
  omega

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    (1 < m) ↔ (1 ≤ m) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    (1 < m) ↔ (1 ≤ m) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    (1 < m) ↔ (1 ≤ m) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    (1 < m) ↔ (1 ≤ m) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    (1 < m) ↔ (1 ≤ m) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    (1 < m) ↔ (1 ≤ m) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (1 ≤ m)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (1 ≤ m)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (1 ≤ m)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (1 ≤ m)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (1 ≤ m)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (1 ≤ m)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≥ m

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≥ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≥ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≥ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≥ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≥ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≥ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≥ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≥ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≥ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≥ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≥ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≥ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≥ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≥ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hm : m > 1) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (1 < m) ↔ (m > 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (1 < m) ↔ (m > 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (1 < m) ↔ (m > 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (1 < m) ↔ (m > 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (1 < m) ↔ (m > 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (1 < m) ↔ (m > 1) := by
  omega

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (1 < m) ↔ (m > 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (1 < m) ↔ (m > 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) ↔
    (∀ (n m : ℕ) (hm : m > 1) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) ↔
    (∀ (n m : ℕ) (hm : m > 1) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) ↔
    (∀ (n m : ℕ) (hm : m > 1) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) ↔
    (∀ (n m : ℕ) (hm : m > 1) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), m ≥ fortunateNumber n

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (fortunateNumber n ≤ m) ↔ (m ≥ fortunateNumber n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (fortunateNumber n ≤ m) ↔ (m ≥ fortunateNumber n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (fortunateNumber n ≤ m) ↔ (m ≥ fortunateNumber n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (fortunateNumber n ≤ m) ↔ (m ≥ fortunateNumber n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (fortunateNumber n ≤ m) ↔ (m ≥ fortunateNumber n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (fortunateNumber n ≤ m) ↔ (m ≥ fortunateNumber n) := by
  omega

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (fortunateNumber n ≤ m) ↔ (m ≥ fortunateNumber n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (fortunateNumber n ≤ m) ↔ (m ≥ fortunateNumber n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) ↔
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), m ≥ fortunateNumber n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) ↔
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), m ≥ fortunateNumber n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) ↔
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), m ≥ fortunateNumber n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) ↔
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), m ≥ fortunateNumber n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) (hm : 1 < m), fortunateNumber n ≤ m

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) ↔
    (∀ (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) (hm : 1 < m), fortunateNumber n ≤ m) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) ↔
    (∀ (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) (hm : 1 < m), fortunateNumber n ≤ m) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) ↔
    (∀ (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) (hm : 1 < m), fortunateNumber n ≤ m) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) ↔
    (∀ (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) (hm : 1 < m), fortunateNumber n ≤ m) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hm₀ : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) ↔
    (∀ (n m : ℕ) (hm₀ : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) ↔
    (∀ (n m : ℕ) (hm₀ : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) ↔
    (∀ (n m : ℕ) (hm₀ : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) ↔
    (∀ (n m : ℕ) (hm₀ : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hm : ¬(m ≤ 1)) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (1 < m) ↔ (¬(m ≤ 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (1 < m) ↔ (¬(m ≤ 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (1 < m) ↔ (¬(m ≤ 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (1 < m) ↔ (¬(m ≤ 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (1 < m) ↔ (¬(m ≤ 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (1 < m) ↔ (¬(m ≤ 1)) := by
  omega

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (1 < m) ↔ (¬(m ≤ 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (1 < m) ↔ (¬(m ≤ 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) ↔
    (∀ (n m : ℕ) (hm : ¬(m ≤ 1)) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) ↔
    (∀ (n m : ℕ) (hm : ¬(m ≤ 1)) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) ↔
    (∀ (n m : ℕ) (hm : ¬(m ≤ 1)) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) ↔
    (∀ (n m : ℕ) (hm : ¬(m ≤ 1)) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hm : 2 ≤ m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (1 < m) ↔ (2 ≤ m) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (1 < m) ↔ (2 ≤ m) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (1 < m) ↔ (2 ≤ m) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (1 < m) ↔ (2 ≤ m) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (1 < m) ↔ (2 ≤ m) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (1 < m) ↔ (2 ≤ m) := by
  omega

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (1 < m) ↔ (2 ≤ m) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n m : ℕ) :
    (1 < m) ↔ (2 ≤ m) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) ↔
    (∀ (n m : ℕ) (hm : 2 ≤ m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) ↔
    (∀ (n m : ℕ) (hm : 2 ≤ m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) ↔
    (∀ (n m : ℕ) (hm : 2 ≤ m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) ↔
    (∀ (n m : ℕ) (hm : 2 ≤ m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hm : m > 1) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n < m

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : m > 1) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n < m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : m > 1) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n < m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : m > 1) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n < m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : m > 1) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n < m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : m > 1) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n < m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : m > 1) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n < m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : m > 1) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n < m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hm : m ≥ 1) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : m ≥ 1) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : m ≥ 1) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : m ≥ 1) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : m ≥ 1) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : m ≥ 1) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : m ≥ 1) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : m ≥ 1) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    (1 < m) ↔ (m ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    (1 < m) ↔ (m ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    (1 < m) ↔ (m ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    (1 < m) ↔ (m ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    (1 < m) ↔ (m ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    (1 < m) ↔ (m ≥ 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    (1 < m) ↔ (m ≥ 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (m ≥ 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (m ≥ 1))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (m ≥ 1))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (m ≥ 1))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (m ≥ 1))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (m ≥ 1))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (m ≥ 1))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (m ≥ 1))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (m ≥ 1))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (m ≥ 1))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (m ≥ 1))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (m ≥ 1))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (m ≥ 1))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (m ≥ 1))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (m ≥ 1))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (m ≥ 1))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (m ≥ 1))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (m ≥ 1))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (m ≥ 1))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (m ≥ 1))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (m ≥ 1))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (m ≥ 1))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (m ≥ 1))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (m ≥ 1))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (m ≥ 1))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (m ≥ 1))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (m ≥ 1))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (m ≥ 1))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (m ≥ 1))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (m ≥ 1))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (m ≥ 1))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (m ≥ 1))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (m ≥ 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (m ≥ 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (m ≥ 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (m ≥ 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (m ≥ 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (m ≥ 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hm : m > 1) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≥ m

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : m > 1) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≥ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : m > 1) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≥ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : m > 1) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≥ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : m > 1) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≥ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : m > 1) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≥ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : m > 1) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≥ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : m > 1) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≥ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : m > 1) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≥ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : m > 1) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≥ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : m > 1) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≥ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : m > 1) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≥ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : m > 1) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≥ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : m > 1) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≥ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : m > 1) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≥ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), m > fortunateNumber n

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), m > fortunateNumber n) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), m > fortunateNumber n) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), m > fortunateNumber n) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), m > fortunateNumber n) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), m > fortunateNumber n) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), m > fortunateNumber n) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), m > fortunateNumber n) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m > fortunateNumber n)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m > fortunateNumber n)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m > fortunateNumber n)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m > fortunateNumber n)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m > fortunateNumber n)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m > fortunateNumber n)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m > fortunateNumber n)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m > fortunateNumber n)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m > fortunateNumber n)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m > fortunateNumber n)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m > fortunateNumber n)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m > fortunateNumber n)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m > fortunateNumber n)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m > fortunateNumber n)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m > fortunateNumber n)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m > fortunateNumber n)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m > fortunateNumber n)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m > fortunateNumber n)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m > fortunateNumber n)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m > fortunateNumber n)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m > fortunateNumber n)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m > fortunateNumber n)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m > fortunateNumber n)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m > fortunateNumber n)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m > fortunateNumber n)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m > fortunateNumber n)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m > fortunateNumber n)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m > fortunateNumber n)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m > fortunateNumber n)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m > fortunateNumber n)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m > fortunateNumber n)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m > fortunateNumber n)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m > fortunateNumber n)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m > fortunateNumber n)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m > fortunateNumber n)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m > fortunateNumber n)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m > fortunateNumber n)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m > fortunateNumber n)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m > fortunateNumber n)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m > fortunateNumber n)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m > fortunateNumber n)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m > fortunateNumber n)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m > fortunateNumber n)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m > fortunateNumber n)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m > fortunateNumber n)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m > fortunateNumber n)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m > fortunateNumber n)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m > fortunateNumber n)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m > fortunateNumber n)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m > fortunateNumber n)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m > fortunateNumber n)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m > fortunateNumber n)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m > fortunateNumber n)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m > fortunateNumber n)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m > fortunateNumber n)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m > fortunateNumber n)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m > fortunateNumber n)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m > fortunateNumber n)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m > fortunateNumber n)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m > fortunateNumber n)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m > fortunateNumber n)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m > fortunateNumber n)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m > fortunateNumber n)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m > fortunateNumber n)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hm : 1 ≤ m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), m ≥ fortunateNumber n

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 ≤ m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), m ≥ fortunateNumber n) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 ≤ m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), m ≥ fortunateNumber n) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 ≤ m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), m ≥ fortunateNumber n) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 ≤ m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), m ≥ fortunateNumber n) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 ≤ m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), m ≥ fortunateNumber n) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 ≤ m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), m ≥ fortunateNumber n) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 ≤ m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), m ≥ fortunateNumber n) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    (1 < m) ↔ (1 ≤ m) := by
  omega

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    (1 < m) ↔ (1 ≤ m) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    (1 < m) ↔ (1 ≤ m) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    (1 < m) ↔ (1 ≤ m) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    (1 < m) ↔ (1 ≤ m) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    (1 < m) ↔ (1 ≤ m) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    (1 < m) ↔ (1 ≤ m) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (1 ≤ m))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (1 ≤ m)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (1 ≤ m)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (1 ≤ m)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (1 ≤ m)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (1 ≤ m)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (1 ≤ m)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), m ≤ fortunateNumber n

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), m ≤ fortunateNumber n) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), m ≤ fortunateNumber n) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), m ≤ fortunateNumber n) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), m ≤ fortunateNumber n) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), m ≤ fortunateNumber n) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), m ≤ fortunateNumber n) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), m ≤ fortunateNumber n) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), m ≤ fortunateNumber n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), m ≤ fortunateNumber n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), m ≤ fortunateNumber n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), m ≤ fortunateNumber n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), m ≤ fortunateNumber n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), m ≤ fortunateNumber n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), m ≤ fortunateNumber n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m ≤ fortunateNumber n)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m ≤ fortunateNumber n)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m ≤ fortunateNumber n)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m ≤ fortunateNumber n)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m ≤ fortunateNumber n)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m ≤ fortunateNumber n)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m ≤ fortunateNumber n)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m ≤ fortunateNumber n)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m ≤ fortunateNumber n)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m ≤ fortunateNumber n)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m ≤ fortunateNumber n)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m ≤ fortunateNumber n)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m ≤ fortunateNumber n)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m ≤ fortunateNumber n)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m ≤ fortunateNumber n)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m ≤ fortunateNumber n)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m ≤ fortunateNumber n)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m ≤ fortunateNumber n)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m ≤ fortunateNumber n)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m ≤ fortunateNumber n)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m ≤ fortunateNumber n)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m ≤ fortunateNumber n)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m ≤ fortunateNumber n)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m ≤ fortunateNumber n)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m ≤ fortunateNumber n)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m ≤ fortunateNumber n)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m ≤ fortunateNumber n)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m ≤ fortunateNumber n)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m ≤ fortunateNumber n)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m ≤ fortunateNumber n)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m ≤ fortunateNumber n)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(m ≤ fortunateNumber n)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m ≤ fortunateNumber n)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m ≤ fortunateNumber n)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m ≤ fortunateNumber n)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m ≤ fortunateNumber n)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m ≤ fortunateNumber n)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m ≤ fortunateNumber n)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m ≤ fortunateNumber n)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m ≤ fortunateNumber n)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m ≤ fortunateNumber n)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m ≤ fortunateNumber n)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m ≤ fortunateNumber n)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m ≤ fortunateNumber n)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m ≤ fortunateNumber n)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m ≤ fortunateNumber n)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m ≤ fortunateNumber n)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m ≤ fortunateNumber n)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m ≤ fortunateNumber n)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m ≤ fortunateNumber n)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m ≤ fortunateNumber n)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m ≤ fortunateNumber n)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m ≤ fortunateNumber n)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m ≤ fortunateNumber n)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m ≤ fortunateNumber n)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m ≤ fortunateNumber n)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m ≤ fortunateNumber n)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m ≤ fortunateNumber n)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m ≤ fortunateNumber n)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m ≤ fortunateNumber n)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m ≤ fortunateNumber n)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m ≤ fortunateNumber n)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m ≤ fortunateNumber n)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (m ≤ fortunateNumber n)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hm : 2 ≤ m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n < m

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 2 ≤ m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n < m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 2 ≤ m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n < m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 2 ≤ m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n < m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 2 ≤ m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n < m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 2 ≤ m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n < m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 2 ≤ m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n < m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 2 ≤ m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n < m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n < m)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n < m)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hm : 2 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 2 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 2 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 2 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 2 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 2 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 2 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 2 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    (1 < m) ↔ (2 < m) := by
  omega

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    (1 < m) ↔ (2 < m) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    (1 < m) ↔ (2 < m) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    (1 < m) ↔ (2 < m) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    (1 < m) ↔ (2 < m) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    (1 < m) ↔ (2 < m) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    (1 < m) ↔ (2 < m) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (2 < m))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (2 < m))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (2 < m))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (2 < m))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (2 < m))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (2 < m))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (2 < m))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (2 < m))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (2 < m))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (2 < m))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (2 < m))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (2 < m))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (2 < m))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (2 < m))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (2 < m))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (2 < m))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (2 < m))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (2 < m))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (2 < m))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (2 < m))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (2 < m))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (2 < m))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (2 < m))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (2 < m))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (2 < m))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (2 < m))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (2 < m))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (2 < m))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (2 < m))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (2 < m))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (2 < m))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (2 < m))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (2 < m)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (2 < m)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (2 < m)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (2 < m)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (2 < m)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (2 < m)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hm : 2 ≤ m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≥ m

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 2 ≤ m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≥ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 2 ≤ m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≥ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 2 ≤ m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≥ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 2 ≤ m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≥ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 2 ≤ m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≥ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 2 ≤ m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≥ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 2 ≤ m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≥ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 2 ≤ m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≥ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 2 ≤ m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≥ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 2 ≤ m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≥ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 2 ≤ m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≥ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 2 ≤ m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≥ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 2 ≤ m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≥ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 2 ≤ m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≥ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (1 < m) ∧ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬(fortunateNumber n ≥ m)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), ¬((fortunateNumber n ≤ m) ↔ (fortunateNumber n ≥ m)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) →
    (∀ (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)), fortunateNumber n ≤ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    (1 < m) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    (1 < m) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    (1 < m) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    (1 < m) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    (1 < m) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    (1 < m) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    (1 < m) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (m : ℕ), (Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) ∧ (¬((1 < m) ↔ (True))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 < m) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n m : ℕ) (hm : 1 < m) (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
