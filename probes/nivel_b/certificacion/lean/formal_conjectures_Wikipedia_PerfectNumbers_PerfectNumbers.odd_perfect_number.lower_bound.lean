import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Perfect numbers

A perfect number is a positive integer that equals the sum of its proper divisors
(i.e., all its positive divisors excluding the number itself).

For example, 6 is perfect because its proper divisors are 1, 2, and 3, and 1 + 2 + 3 = 6.
Similarly, 28 is perfect because 1 + 2 + 4 + 7 + 14 = 28.

All known perfect numbers are even. Several open problems about perfect numbers are
formalised here:

* Are there infinitely many perfect numbers?
* Are there infinitely many even perfect numbers?
* Do odd perfect numbers exist?

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Perfect_number)
- [Wikipedia, Odd perfect numbers](https://en.wikipedia.org/wiki/Perfect_number#Odd_perfect_numbers)
-/

section

namespace PerfectNumbers

open Nat

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) →
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) →
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) →
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) →
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) →
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) →
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) →
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ (n > 10^1500)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ (n > 10^1500)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ (n > 10^1500)) :=
  ⟨(11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ (n > 10^1500)) :=
  ⟨(1500 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ (n > 10^1500)) :=
  ⟨(1499 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ (n > 10^1500)) :=
  ⟨(1501 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ (n > 10^1500)) :=
  ⟨(101 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ (n > 10^1500)) :=
  ⟨(100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ (n > 10^1500)) :=
  ⟨(102 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ (n > 10^1500)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ (n > 10^1500)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ (n > 10^1500)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ (n > 10^1500)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ (n > 10^1500)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 11^1500 ∧ (n.primeFactorsList).length ≥ 101

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 11^1500 ∧ (n.primeFactorsList).length ≥ 101) →
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 11^1500 ∧ (n.primeFactorsList).length ≥ 101) →
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 11^1500 ∧ (n.primeFactorsList).length ≥ 101) →
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 11^1500 ∧ (n.primeFactorsList).length ≥ 101) →
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 11^1500 ∧ (n.primeFactorsList).length ≥ 101) →
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 11^1500 ∧ (n.primeFactorsList).length ≥ 101) →
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 11^1500 ∧ (n.primeFactorsList).length ≥ 101) →
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) →
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 11^1500 ∧ (n.primeFactorsList).length ≥ 101) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) →
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 11^1500 ∧ (n.primeFactorsList).length ≥ 101) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) →
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 11^1500 ∧ (n.primeFactorsList).length ≥ 101) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) →
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 11^1500 ∧ (n.primeFactorsList).length ≥ 101) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) →
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 11^1500 ∧ (n.primeFactorsList).length ≥ 101) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) →
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 11^1500 ∧ (n.primeFactorsList).length ≥ 101) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) →
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 11^1500 ∧ (n.primeFactorsList).length ≥ 101) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (Perfect n) ∧ (¬(n > 11^1500 ∧ (n.primeFactorsList).length ≥ 101)) :=
  ⟨(11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (Perfect n) ∧ (¬(n > 11^1500 ∧ (n.primeFactorsList).length ≥ 101)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (Perfect n) ∧ (¬(n > 11^1500 ∧ (n.primeFactorsList).length ≥ 101)) :=
  ⟨(12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (Perfect n) ∧ (¬(n > 11^1500 ∧ (n.primeFactorsList).length ≥ 101)) :=
  ⟨(1500 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (Perfect n) ∧ (¬(n > 11^1500 ∧ (n.primeFactorsList).length ≥ 101)) :=
  ⟨(1499 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (Perfect n) ∧ (¬(n > 11^1500 ∧ (n.primeFactorsList).length ≥ 101)) :=
  ⟨(1501 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (Perfect n) ∧ (¬(n > 11^1500 ∧ (n.primeFactorsList).length ≥ 101)) :=
  ⟨(101 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (Perfect n) ∧ (¬(n > 11^1500 ∧ (n.primeFactorsList).length ≥ 101)) :=
  ⟨(100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (Perfect n) ∧ (¬(n > 11^1500 ∧ (n.primeFactorsList).length ≥ 101)) :=
  ⟨(102 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (Perfect n) ∧ (¬(n > 11^1500 ∧ (n.primeFactorsList).length ≥ 101)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (Perfect n) ∧ (¬(n > 11^1500 ∧ (n.primeFactorsList).length ≥ 101)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (Perfect n) ∧ (¬(n > 11^1500 ∧ (n.primeFactorsList).length ≥ 101)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (Perfect n) ∧ (¬(n > 11^1500 ∧ (n.primeFactorsList).length ≥ 101)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (Perfect n) ∧ (¬(n > 11^1500 ∧ (n.primeFactorsList).length ≥ 101)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ (n > 11^1500 ∧ (n.primeFactorsList).length ≥ 101)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ (n > 11^1500 ∧ (n.primeFactorsList).length ≥ 101)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ (n > 11^1500 ∧ (n.primeFactorsList).length ≥ 101)) :=
  ⟨(11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ (n > 11^1500 ∧ (n.primeFactorsList).length ≥ 101)) :=
  ⟨(1500 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ (n > 11^1500 ∧ (n.primeFactorsList).length ≥ 101)) :=
  ⟨(1499 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ (n > 11^1500 ∧ (n.primeFactorsList).length ≥ 101)) :=
  ⟨(1501 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ (n > 11^1500 ∧ (n.primeFactorsList).length ≥ 101)) :=
  ⟨(101 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ (n > 11^1500 ∧ (n.primeFactorsList).length ≥ 101)) :=
  ⟨(100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ (n > 11^1500 ∧ (n.primeFactorsList).length ≥ 101)) :=
  ⟨(102 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ (n > 11^1500 ∧ (n.primeFactorsList).length ≥ 101)) :=
  ⟨(12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ (n > 11^1500 ∧ (n.primeFactorsList).length ≥ 101)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ (n > 11^1500 ∧ (n.primeFactorsList).length ≥ 101)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ (n > 11^1500 ∧ (n.primeFactorsList).length ≥ 101)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ (n > 11^1500 ∧ (n.primeFactorsList).length ≥ 101)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ (n > 11^1500 ∧ (n.primeFactorsList).length ≥ 101)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hp : Perfect n) (hn : Odd n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔
    (∀ (n : ℕ) (hp : Perfect n) (hn : Odd n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔
    (∀ (n : ℕ) (hp : Perfect n) (hn : Odd n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔
    (∀ (n : ℕ) (hp : Perfect n) (hn : Odd n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔
    (∀ (n : ℕ) (hp : Perfect n) (hn : Odd n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), (n.primeFactorsList).length ≥ 101 ∧ n > 10^1500

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ ((n.primeFactorsList).length ≥ 101 ∧ n > 10^1500) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ ((n.primeFactorsList).length ≥ 101 ∧ n > 10^1500) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ ((n.primeFactorsList).length ≥ 101 ∧ n > 10^1500) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ ((n.primeFactorsList).length ≥ 101 ∧ n > 10^1500) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ ((n.primeFactorsList).length ≥ 101 ∧ n > 10^1500) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ ((n.primeFactorsList).length ≥ 101 ∧ n > 10^1500) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ ((n.primeFactorsList).length ≥ 101 ∧ n > 10^1500) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ ((n.primeFactorsList).length ≥ 101 ∧ n > 10^1500) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), (n.primeFactorsList).length ≥ 101 ∧ n > 10^1500) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), (n.primeFactorsList).length ≥ 101 ∧ n > 10^1500) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), (n.primeFactorsList).length ≥ 101 ∧ n > 10^1500) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), (n.primeFactorsList).length ≥ 101 ∧ n > 10^1500) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn₀ : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔
    (∀ (n : ℕ) (hn₀ : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔
    (∀ (n : ℕ) (hn₀ : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔
    (∀ (n : ℕ) (hn₀ : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔
    (∀ (n : ℕ) (hn₀ : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), (n.primeFactorsList).length ≥ 101

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) →
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), (n.primeFactorsList).length ≥ 101) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) →
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), (n.primeFactorsList).length ≥ 101) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) →
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), (n.primeFactorsList).length ≥ 101) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) →
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), (n.primeFactorsList).length ≥ 101) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) →
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), (n.primeFactorsList).length ≥ 101) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) →
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), (n.primeFactorsList).length ≥ 101) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) →
    (∀ (n : ℕ) (hn : Odd n) (hp : Perfect n), (n.primeFactorsList).length ≥ 101) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ ((n.primeFactorsList).length ≥ 101)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ ((n.primeFactorsList).length ≥ 101)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ ((n.primeFactorsList).length ≥ 101)) :=
  ⟨(11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ ((n.primeFactorsList).length ≥ 101)) :=
  ⟨(1500 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ ((n.primeFactorsList).length ≥ 101)) :=
  ⟨(1499 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ ((n.primeFactorsList).length ≥ 101)) :=
  ⟨(1501 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ ((n.primeFactorsList).length ≥ 101)) :=
  ⟨(101 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ ((n.primeFactorsList).length ≥ 101)) :=
  ⟨(100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ ((n.primeFactorsList).length ≥ 101)) :=
  ⟨(102 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ ((n.primeFactorsList).length ≥ 101)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ ((n.primeFactorsList).length ≥ 101)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ ((n.primeFactorsList).length ≥ 101)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ ((n.primeFactorsList).length ≥ 101)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 10^1500 ∧ (n.primeFactorsList).length ≥ 101) ↔ ((n.primeFactorsList).length ≥ 101)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hp : Perfect n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hp : Perfect n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hp : Perfect n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hp : Perfect n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hp : Perfect n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
