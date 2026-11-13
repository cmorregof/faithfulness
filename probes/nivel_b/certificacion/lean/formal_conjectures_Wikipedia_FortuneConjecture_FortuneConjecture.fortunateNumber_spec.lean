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
  ∀ (n : ℕ), 1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), 1 ≤ fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) →
    (∀ (n : ℕ), 1 ≤ fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) →
    (∀ (n : ℕ), 1 ≤ fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) →
    (∀ (n : ℕ), 1 ≤ fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) →
    (∀ (n : ℕ), 1 ≤ fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) →
    (∀ (n : ℕ), 1 ≤ fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) →
    (∀ (n : ℕ), 1 ≤ fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) →
    (∀ (n : ℕ), 1 ≤ fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) ↔ (1 ≤ fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) ↔ (1 ≤ fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) ↔ (1 ≤ fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) ↔ (1 ≤ fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) ↔ (1 ≤ fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) ↔ (1 ≤ fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), 1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), 1 < fortunateNumber n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) →
    (∀ (n : ℕ), 1 < fortunateNumber n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) →
    (∀ (n : ℕ), 1 < fortunateNumber n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) →
    (∀ (n : ℕ), 1 < fortunateNumber n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) →
    (∀ (n : ℕ), 1 < fortunateNumber n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) →
    (∀ (n : ℕ), 1 < fortunateNumber n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) →
    (∀ (n : ℕ), 1 < fortunateNumber n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) →
    (∀ (n : ℕ), 1 < fortunateNumber n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) ↔ (1 < fortunateNumber n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) ↔ (1 < fortunateNumber n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) ↔ (1 < fortunateNumber n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) ↔ (1 < fortunateNumber n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) ↔ (1 < fortunateNumber n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) ↔ (1 < fortunateNumber n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), 1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), 1 > fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 1 > fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) →
    (∀ (n : ℕ), 1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 1 > fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) →
    (∀ (n : ℕ), 1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 1 > fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) →
    (∀ (n : ℕ), 1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 1 > fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) →
    (∀ (n : ℕ), 1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 1 > fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) →
    (∀ (n : ℕ), 1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 1 > fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) →
    (∀ (n : ℕ), 1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 1 > fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) →
    (∀ (n : ℕ), 1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) →
    (∀ (n : ℕ), 1 > fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) →
    (∀ (n : ℕ), 1 > fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) →
    (∀ (n : ℕ), 1 > fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) →
    (∀ (n : ℕ), 1 > fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) →
    (∀ (n : ℕ), 1 > fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) →
    (∀ (n : ℕ), 1 > fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) →
    (∀ (n : ℕ), 1 > fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(1 > fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(1 > fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(1 > fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(1 > fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(1 > fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(1 > fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) ↔ (1 > fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) ↔ (1 > fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) ↔ (1 > fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) ↔ (1 > fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) ↔ (1 > fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) ↔ (1 > fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), 1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n) ∧ 1 < fortunateNumber n

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) ↔ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n) ∧ 1 < fortunateNumber n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) ↔ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n) ∧ 1 < fortunateNumber n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) ↔ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n) ∧ 1 < fortunateNumber n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) ↔ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n) ∧ 1 < fortunateNumber n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) ↔ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n) ∧ 1 < fortunateNumber n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) ↔ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n) ∧ 1 < fortunateNumber n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) ↔ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n) ∧ 1 < fortunateNumber n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) ↔ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n) ∧ 1 < fortunateNumber n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) ↔
    (∀ (n : ℕ), Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n) ∧ 1 < fortunateNumber n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) ↔
    (∀ (n : ℕ), Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n) ∧ 1 < fortunateNumber n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) ↔
    (∀ (n : ℕ), Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n) ∧ 1 < fortunateNumber n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) ↔
    (∀ (n : ℕ), Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n) ∧ 1 < fortunateNumber n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), 1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) →
    (∀ (n : ℕ), Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) →
    (∀ (n : ℕ), Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) →
    (∀ (n : ℕ), Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) →
    (∀ (n : ℕ), Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) →
    (∀ (n : ℕ), Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) →
    (∀ (n : ℕ), Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), 1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) →
    (∀ (n : ℕ), Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) ↔ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) ↔ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) ↔ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) ↔ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) ↔ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n)) ↔ (Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n))) :=
  ⟨(10 : ℕ), by norm_num⟩

#eval "FIN_CERTIFICAR"
