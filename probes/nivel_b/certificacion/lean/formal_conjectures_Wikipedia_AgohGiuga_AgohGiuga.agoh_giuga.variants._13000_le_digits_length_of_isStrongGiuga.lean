import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Data.Nat.Prime.Composite
/-!
# Agoh-Giuga conjecture

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Agoh-Giuga_conjecture)
-/

section

open scoped Nat
/-

The **Agoh-Giuga Conjecture**.

References:
* Wikipedia: https://en.wikipedia.org/wiki/Agoh-Giuga_conjecture
* Wikipedia: https://en.wikipedia.org/wiki/Giuga_number
* G. Giuga, _Su una presumibile proprieta caratteristica dei numeri primi_
* E. Bedocchi, _Note on a conjecture about prime numbers_
* D. Borwein, J. M. Borwein, P. B. Borwein, and R. Girgensohn, _Giuga’s conjecture on primality_
* V. Tipu, _A Note on Giuga’s Conjecture_

-/

namespace AgohGiuga

/--
The **Agoh-Giuga Conjecture**, Agoh's formulation.
An integer `p ≥ 2` is prime if and only if we have
`p*B_{p-1} ≡ -1 [MOD p]`
-/
def AgohGiugaCongr : Prop :=
  ∀ p ≥ 2, p.Prime ↔ ∃ (k : ℤ),
  let B := bernoulli' (p - 1)
  p * B.num + B.den = k * p^2

/--
The **Agoh-Giuga Conjecture**, Giuga's formulation.
An integer `p ≥ 2` is prime if and only if it satisfies the congruence
`∑_{i=1}^{p-1} i^{p-1} ≡ -1 [MOD p]`.
-/
def AgohGiugaSum : Prop := ∀ p ≥ 2, p.Prime ↔
  p ∣ 1 + ∑ i ∈ Finset.Ioo 0 p, i^(p - 1 : ℕ)

-- Formalisation note: refers to a Giuga number in the sense of
-- https://en.wikipedia.org/wiki/Giuga_number
/--
A (weak) Giuga number is a composite number $n$ such that
$$\sum_{i=1}^{n - 1}i^{\varphi(n)} \equiv -1\pmod{n}$$.
-/
def IsWeakGiuga (n : ℕ) : Prop :=
    n.Composite ∧ n ∣ 1 + ∑ i ∈ Finset.Ioo 0 n, i ^ φ n

-- Formalisation note: refers to a Giuga number in the sense of
-- https://www.cambridge.org/core/services/aop-cambridge-core/content/view/8A6841B3FDA442A8FAEC89AA702C16F6/S0008439500007244a.pdf/note_on_giugas_conjecture.pdf
/--
A (strong) Giuga number is a composite number $n$ such that
$$\sum_{i=1}^{n - 1}i^{n - 1} \equiv -1\pmod{n}$$-/
def IsStrongGiuga (n : ℕ) : Prop :=
    n.Composite ∧ n ∣ 1 + ∑ i ∈ Finset.Ioo 0 n, i ^ (n - 1)

-- Wikipedia URL: https://en.wikipedia.org/wiki/Carmichael_number

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 < (Nat.digits 10 a).length

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 < (Nat.digits 10 a).length) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 < (Nat.digits 10 a).length) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 < (Nat.digits 10 a).length) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 < (Nat.digits 10 a).length) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 < (Nat.digits 10 a).length) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 < (Nat.digits 10 a).length) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 < (Nat.digits 10 a).length) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬(13000 < (Nat.digits 10 a).length)) :=
  ⟨(13000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬(13000 < (Nat.digits 10 a).length)) :=
  ⟨(12999 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬(13000 < (Nat.digits 10 a).length)) :=
  ⟨(13001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬(13000 < (Nat.digits 10 a).length)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬(13000 < (Nat.digits 10 a).length)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬(13000 < (Nat.digits 10 a).length)) :=
  ⟨(11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬(13000 < (Nat.digits 10 a).length)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬(13000 < (Nat.digits 10 a).length)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬(13000 < (Nat.digits 10 a).length)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬(13000 < (Nat.digits 10 a).length)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬(13000 < (Nat.digits 10 a).length)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ (13000 < (Nat.digits 10 a).length)) :=
  ⟨(13000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ (13000 < (Nat.digits 10 a).length)) :=
  ⟨(12999 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ (13000 < (Nat.digits 10 a).length)) :=
  ⟨(13001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ (13000 < (Nat.digits 10 a).length)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ (13000 < (Nat.digits 10 a).length)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ (13000 < (Nat.digits 10 a).length)) :=
  ⟨(11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ (13000 < (Nat.digits 10 a).length)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ (13000 < (Nat.digits 10 a).length)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ (13000 < (Nat.digits 10 a).length)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ (13000 < (Nat.digits 10 a).length)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ (13000 < (Nat.digits 10 a).length)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℕ) (ha : IsStrongGiuga a), 13001 ≤ (Nat.digits 10 a).length

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13001 ≤ (Nat.digits 10 a).length) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13001 ≤ (Nat.digits 10 a).length) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13001 ≤ (Nat.digits 10 a).length) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13001 ≤ (Nat.digits 10 a).length) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13001 ≤ (Nat.digits 10 a).length) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13001 ≤ (Nat.digits 10 a).length) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13001 ≤ (Nat.digits 10 a).length) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬(13001 ≤ (Nat.digits 10 a).length)) :=
  ⟨(13001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬(13001 ≤ (Nat.digits 10 a).length)) :=
  ⟨(13000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬(13001 ≤ (Nat.digits 10 a).length)) :=
  ⟨(13002 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬(13001 ≤ (Nat.digits 10 a).length)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬(13001 ≤ (Nat.digits 10 a).length)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬(13001 ≤ (Nat.digits 10 a).length)) :=
  ⟨(11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬(13001 ≤ (Nat.digits 10 a).length)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬(13001 ≤ (Nat.digits 10 a).length)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬(13001 ≤ (Nat.digits 10 a).length)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬(13001 ≤ (Nat.digits 10 a).length)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬(13001 ≤ (Nat.digits 10 a).length)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ (13001 ≤ (Nat.digits 10 a).length)) :=
  ⟨(13000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ (13001 ≤ (Nat.digits 10 a).length)) :=
  ⟨(12999 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ (13001 ≤ (Nat.digits 10 a).length)) :=
  ⟨(13001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ (13001 ≤ (Nat.digits 10 a).length)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ (13001 ≤ (Nat.digits 10 a).length)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ (13001 ≤ (Nat.digits 10 a).length)) :=
  ⟨(11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ (13001 ≤ (Nat.digits 10 a).length)) :=
  ⟨(13002 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ (13001 ≤ (Nat.digits 10 a).length)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ (13001 ≤ (Nat.digits 10 a).length)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ (13001 ≤ (Nat.digits 10 a).length)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ (13001 ≤ (Nat.digits 10 a).length)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ (13001 ≤ (Nat.digits 10 a).length)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≥ (Nat.digits 10 a).length

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≥ (Nat.digits 10 a).length) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≥ (Nat.digits 10 a).length) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≥ (Nat.digits 10 a).length) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≥ (Nat.digits 10 a).length) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≥ (Nat.digits 10 a).length) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≥ (Nat.digits 10 a).length) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≥ (Nat.digits 10 a).length) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≥ (Nat.digits 10 a).length) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≥ (Nat.digits 10 a).length) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≥ (Nat.digits 10 a).length) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≥ (Nat.digits 10 a).length) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≥ (Nat.digits 10 a).length) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≥ (Nat.digits 10 a).length) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≥ (Nat.digits 10 a).length) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬(13000 ≥ (Nat.digits 10 a).length)) :=
  ⟨(13000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬(13000 ≥ (Nat.digits 10 a).length)) :=
  ⟨(12999 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬(13000 ≥ (Nat.digits 10 a).length)) :=
  ⟨(13001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬(13000 ≥ (Nat.digits 10 a).length)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬(13000 ≥ (Nat.digits 10 a).length)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬(13000 ≥ (Nat.digits 10 a).length)) :=
  ⟨(11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬(13000 ≥ (Nat.digits 10 a).length)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬(13000 ≥ (Nat.digits 10 a).length)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬(13000 ≥ (Nat.digits 10 a).length)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬(13000 ≥ (Nat.digits 10 a).length)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬(13000 ≥ (Nat.digits 10 a).length)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ (13000 ≥ (Nat.digits 10 a).length)) :=
  ⟨(13000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ (13000 ≥ (Nat.digits 10 a).length)) :=
  ⟨(12999 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ (13000 ≥ (Nat.digits 10 a).length)) :=
  ⟨(13001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ (13000 ≥ (Nat.digits 10 a).length)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ (13000 ≥ (Nat.digits 10 a).length)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ (13000 ≥ (Nat.digits 10 a).length)) :=
  ⟨(11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ (13000 ≥ (Nat.digits 10 a).length)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ (13000 ≥ (Nat.digits 10 a).length)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ (13000 ≥ (Nat.digits 10 a).length)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ (13000 ≥ (Nat.digits 10 a).length)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ (13000 ≥ (Nat.digits 10 a).length)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℕ) (ha : IsStrongGiuga a), (Nat.digits 10 a).length ≥ 13000

set_option maxHeartbeats 200000 in
example (a : ℕ) :
    (13000 ≤ (Nat.digits 10 a).length) ↔ ((Nat.digits 10 a).length ≥ 13000) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (a : ℕ) :
    (13000 ≤ (Nat.digits 10 a).length) ↔ ((Nat.digits 10 a).length ≥ 13000) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (a : ℕ) :
    (13000 ≤ (Nat.digits 10 a).length) ↔ ((Nat.digits 10 a).length ≥ 13000) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (a : ℕ) :
    (13000 ≤ (Nat.digits 10 a).length) ↔ ((Nat.digits 10 a).length ≥ 13000) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (a : ℕ) :
    (13000 ≤ (Nat.digits 10 a).length) ↔ ((Nat.digits 10 a).length ≥ 13000) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (a : ℕ) :
    (13000 ≤ (Nat.digits 10 a).length) ↔ ((Nat.digits 10 a).length ≥ 13000) := by
  omega

set_option maxHeartbeats 200000 in
example (a : ℕ) :
    (13000 ≤ (Nat.digits 10 a).length) ↔ ((Nat.digits 10 a).length ≥ 13000) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (a : ℕ) :
    (13000 ≤ (Nat.digits 10 a).length) ↔ ((Nat.digits 10 a).length ≥ 13000) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) ↔
    (∀ (a : ℕ) (ha : IsStrongGiuga a), (Nat.digits 10 a).length ≥ 13000) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) ↔
    (∀ (a : ℕ) (ha : IsStrongGiuga a), (Nat.digits 10 a).length ≥ 13000) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) ↔
    (∀ (a : ℕ) (ha : IsStrongGiuga a), (Nat.digits 10 a).length ≥ 13000) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) ↔
    (∀ (a : ℕ) (ha : IsStrongGiuga a), (Nat.digits 10 a).length ≥ 13000) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℕ) (ha₀ : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) ↔
    (∀ (a : ℕ) (ha₀ : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) ↔
    (∀ (a : ℕ) (ha₀ : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) ↔
    (∀ (a : ℕ) (ha₀ : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) ↔
    (∀ (a : ℕ) (ha₀ : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℕ) (ha : IsStrongGiuga a), ¬((Nat.digits 10 a).length < 13000)

set_option maxHeartbeats 200000 in
example (a : ℕ) :
    (13000 ≤ (Nat.digits 10 a).length) ↔ (¬((Nat.digits 10 a).length < 13000)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (a : ℕ) :
    (13000 ≤ (Nat.digits 10 a).length) ↔ (¬((Nat.digits 10 a).length < 13000)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (a : ℕ) :
    (13000 ≤ (Nat.digits 10 a).length) ↔ (¬((Nat.digits 10 a).length < 13000)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (a : ℕ) :
    (13000 ≤ (Nat.digits 10 a).length) ↔ (¬((Nat.digits 10 a).length < 13000)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (a : ℕ) :
    (13000 ≤ (Nat.digits 10 a).length) ↔ (¬((Nat.digits 10 a).length < 13000)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (a : ℕ) :
    (13000 ≤ (Nat.digits 10 a).length) ↔ (¬((Nat.digits 10 a).length < 13000)) := by
  omega

set_option maxHeartbeats 200000 in
example (a : ℕ) :
    (13000 ≤ (Nat.digits 10 a).length) ↔ (¬((Nat.digits 10 a).length < 13000)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (a : ℕ) :
    (13000 ≤ (Nat.digits 10 a).length) ↔ (¬((Nat.digits 10 a).length < 13000)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) ↔
    (∀ (a : ℕ) (ha : IsStrongGiuga a), ¬((Nat.digits 10 a).length < 13000)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) ↔
    (∀ (a : ℕ) (ha : IsStrongGiuga a), ¬((Nat.digits 10 a).length < 13000)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) ↔
    (∀ (a : ℕ) (ha : IsStrongGiuga a), ¬((Nat.digits 10 a).length < 13000)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) ↔
    (∀ (a : ℕ) (ha : IsStrongGiuga a), ¬((Nat.digits 10 a).length < 13000)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℕ) (ha : IsStrongGiuga a), (Nat.digits 10 a).length > 13000

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), (Nat.digits 10 a).length > 13000) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), (Nat.digits 10 a).length > 13000) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), (Nat.digits 10 a).length > 13000) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), (Nat.digits 10 a).length > 13000) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), (Nat.digits 10 a).length > 13000) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), (Nat.digits 10 a).length > 13000) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), (Nat.digits 10 a).length > 13000) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬((Nat.digits 10 a).length > 13000)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬((Nat.digits 10 a).length > 13000)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬((Nat.digits 10 a).length > 13000)) :=
  ⟨(11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬((Nat.digits 10 a).length > 13000)) :=
  ⟨(13000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬((Nat.digits 10 a).length > 13000)) :=
  ⟨(12999 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬((Nat.digits 10 a).length > 13000)) :=
  ⟨(13001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬((Nat.digits 10 a).length > 13000)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬((Nat.digits 10 a).length > 13000)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬((Nat.digits 10 a).length > 13000)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬((Nat.digits 10 a).length > 13000)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬((Nat.digits 10 a).length > 13000)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ ((Nat.digits 10 a).length > 13000)) :=
  ⟨(13000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ ((Nat.digits 10 a).length > 13000)) :=
  ⟨(12999 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ ((Nat.digits 10 a).length > 13000)) :=
  ⟨(13001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ ((Nat.digits 10 a).length > 13000)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ ((Nat.digits 10 a).length > 13000)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ ((Nat.digits 10 a).length > 13000)) :=
  ⟨(11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ ((Nat.digits 10 a).length > 13000)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ ((Nat.digits 10 a).length > 13000)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ ((Nat.digits 10 a).length > 13000)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ ((Nat.digits 10 a).length > 13000)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ ((Nat.digits 10 a).length > 13000)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℕ) (ha : IsStrongGiuga a), (Nat.digits 10 a).length ≥ 13001

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), (Nat.digits 10 a).length ≥ 13001) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), (Nat.digits 10 a).length ≥ 13001) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), (Nat.digits 10 a).length ≥ 13001) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), (Nat.digits 10 a).length ≥ 13001) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), (Nat.digits 10 a).length ≥ 13001) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), (Nat.digits 10 a).length ≥ 13001) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), (Nat.digits 10 a).length ≥ 13001) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬((Nat.digits 10 a).length ≥ 13001)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬((Nat.digits 10 a).length ≥ 13001)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬((Nat.digits 10 a).length ≥ 13001)) :=
  ⟨(11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬((Nat.digits 10 a).length ≥ 13001)) :=
  ⟨(13001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬((Nat.digits 10 a).length ≥ 13001)) :=
  ⟨(13000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬((Nat.digits 10 a).length ≥ 13001)) :=
  ⟨(13002 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬((Nat.digits 10 a).length ≥ 13001)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬((Nat.digits 10 a).length ≥ 13001)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬((Nat.digits 10 a).length ≥ 13001)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬((Nat.digits 10 a).length ≥ 13001)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬((Nat.digits 10 a).length ≥ 13001)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ ((Nat.digits 10 a).length ≥ 13001)) :=
  ⟨(13000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ ((Nat.digits 10 a).length ≥ 13001)) :=
  ⟨(12999 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ ((Nat.digits 10 a).length ≥ 13001)) :=
  ⟨(13001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ ((Nat.digits 10 a).length ≥ 13001)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ ((Nat.digits 10 a).length ≥ 13001)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ ((Nat.digits 10 a).length ≥ 13001)) :=
  ⟨(11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ ((Nat.digits 10 a).length ≥ 13001)) :=
  ⟨(13002 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ ((Nat.digits 10 a).length ≥ 13001)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ ((Nat.digits 10 a).length ≥ 13001)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ ((Nat.digits 10 a).length ≥ 13001)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ ((Nat.digits 10 a).length ≥ 13001)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ ((Nat.digits 10 a).length ≥ 13001)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : ℕ) (ha : IsStrongGiuga a), (Nat.digits 10 a).length ≤ 13000

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), (Nat.digits 10 a).length ≤ 13000) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), (Nat.digits 10 a).length ≤ 13000) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), (Nat.digits 10 a).length ≤ 13000) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), (Nat.digits 10 a).length ≤ 13000) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), (Nat.digits 10 a).length ≤ 13000) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), (Nat.digits 10 a).length ≤ 13000) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), (Nat.digits 10 a).length ≤ 13000) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), (Nat.digits 10 a).length ≤ 13000) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), (Nat.digits 10 a).length ≤ 13000) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), (Nat.digits 10 a).length ≤ 13000) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), (Nat.digits 10 a).length ≤ 13000) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), (Nat.digits 10 a).length ≤ 13000) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), (Nat.digits 10 a).length ≤ 13000) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a : ℕ) (ha : IsStrongGiuga a), 13000 ≤ (Nat.digits 10 a).length) →
    (∀ (a : ℕ) (ha : IsStrongGiuga a), (Nat.digits 10 a).length ≤ 13000) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬((Nat.digits 10 a).length ≤ 13000)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬((Nat.digits 10 a).length ≤ 13000)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬((Nat.digits 10 a).length ≤ 13000)) :=
  ⟨(11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬((Nat.digits 10 a).length ≤ 13000)) :=
  ⟨(13000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬((Nat.digits 10 a).length ≤ 13000)) :=
  ⟨(12999 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬((Nat.digits 10 a).length ≤ 13000)) :=
  ⟨(13001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬((Nat.digits 10 a).length ≤ 13000)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬((Nat.digits 10 a).length ≤ 13000)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬((Nat.digits 10 a).length ≤ 13000)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬((Nat.digits 10 a).length ≤ 13000)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), (IsStrongGiuga a) ∧ (¬((Nat.digits 10 a).length ≤ 13000)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ ((Nat.digits 10 a).length ≤ 13000)) :=
  ⟨(13000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ ((Nat.digits 10 a).length ≤ 13000)) :=
  ⟨(12999 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ ((Nat.digits 10 a).length ≤ 13000)) :=
  ⟨(13001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ ((Nat.digits 10 a).length ≤ 13000)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ ((Nat.digits 10 a).length ≤ 13000)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ ((Nat.digits 10 a).length ≤ 13000)) :=
  ⟨(11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ ((Nat.digits 10 a).length ≤ 13000)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ ((Nat.digits 10 a).length ≤ 13000)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ ((Nat.digits 10 a).length ≤ 13000)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ ((Nat.digits 10 a).length ≤ 13000)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((13000 ≤ (Nat.digits 10 a).length) ↔ ((Nat.digits 10 a).length ≤ 13000)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (a : ℕ) (ha : IsStrongGiuga a) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (a : ℕ) (ha : IsStrongGiuga a) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (a : ℕ) (ha : IsStrongGiuga a) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (a : ℕ) (ha : IsStrongGiuga a) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (a : ℕ) (ha : IsStrongGiuga a) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
