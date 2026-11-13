import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Decimal concatenation of a cofactor and the largest prime factor

For a composite positive integer $n$, let $p$ be its largest prime factor. The sequence value
$a(n)$ concatenates the decimal representations of $n/p$ and $p$, in that order. It fixes primes
and one, and is extended here by $a(0)=0$. OEIS A397122 records the prime reached by iterating
this map from each starting value, or $-1$ if no prime is reached.

*References:*
- [OEIS A401006](https://oeis.org/A401006)
- [OEIS A397122](https://oeis.org/A397122)
-/

section

namespace OeisA401006

/-- The number of decimal digits of a natural number, counting zero as one digit. -/
def decimalDigitCount (n : ℕ) : ℕ :=
  if n = 0 then 1 else (Nat.digits 10 n).length

/-- Append the decimal digits of `b` to those of `a`. -/
def decimalAppend (a b : ℕ) : ℕ :=
  a * 10 ^ decimalDigitCount b + b

/-- Zero, one, and primes are fixed; a composite number is replaced by its
cofactor after removing one largest prime factor, followed by that prime factor in decimal. -/
def a (n : ℕ) : ℕ :=
  if n ≤ 1 then n
  else if n.Prime then n
  else decimalAppend (n / n.maxPrimeFac) n.maxPrimeFac

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n ≤ a n

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n ≤ a n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n ≤ a n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n ≤ a n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n ≤ a n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n ≤ a n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n ≤ a n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n ≤ a n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (n ≤ a n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (n ≤ a n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (n ≤ a n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (n ≤ a n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (n ≤ a n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (n ≤ a n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n > a n

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n > a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n > a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n > a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n > a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n > a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n > a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n > a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n > a n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n > a n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n > a n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n > a n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n > a n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n > a n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n > a n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬n.Prime) ∧ (¬(n > a n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬n.Prime) ∧ (¬(n > a n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬n.Prime) ∧ (¬(n > a n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬n.Prime) ∧ (¬(n > a n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬n.Prime) ∧ (¬(n > a n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬n.Prime) ∧ (¬(n > a n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (n > a n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (n > a n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (n > a n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (n > a n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (n > a n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (n > a n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : n > 1) (hprime : ¬n.Prime), n < a n

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 < n) ↔ (n > 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 < n) ↔ (n > 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 < n) ↔ (n > 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 < n) ↔ (n > 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 < n) ↔ (n > 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 < n) ↔ (n > 1) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 < n) ↔ (n > 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 < n) ↔ (n > 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) ↔
    (∀ {n : ℕ} (hn : n > 1) (hprime : ¬n.Prime), n < a n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) ↔
    (∀ {n : ℕ} (hn : n > 1) (hprime : ¬n.Prime), n < a n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) ↔
    (∀ {n : ℕ} (hn : n > 1) (hprime : ¬n.Prime), n < a n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) ↔
    (∀ {n : ℕ} (hn : n > 1) (hprime : ¬n.Prime), n < a n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), a n > n

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (n < a n) ↔ (a n > n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (n < a n) ↔ (a n > n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (n < a n) ↔ (a n > n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (n < a n) ↔ (a n > n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (n < a n) ↔ (a n > n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (n < a n) ↔ (a n > n) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (n < a n) ↔ (a n > n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (n < a n) ↔ (a n > n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) ↔
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), a n > n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) ↔
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), a n > n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) ↔
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), a n > n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) ↔
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), a n > n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hprime : ¬n.Prime) (hn : 1 < n), n < a n

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) ↔
    (∀ {n : ℕ} (hprime : ¬n.Prime) (hn : 1 < n), n < a n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) ↔
    (∀ {n : ℕ} (hprime : ¬n.Prime) (hn : 1 < n), n < a n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) ↔
    (∀ {n : ℕ} (hprime : ¬n.Prime) (hn : 1 < n), n < a n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) ↔
    (∀ {n : ℕ} (hprime : ¬n.Prime) (hn : 1 < n), n < a n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn₀ : 1 < n) (hprime : ¬n.Prime), n < a n

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) ↔
    (∀ {n : ℕ} (hn₀ : 1 < n) (hprime : ¬n.Prime), n < a n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) ↔
    (∀ {n : ℕ} (hn₀ : 1 < n) (hprime : ¬n.Prime), n < a n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) ↔
    (∀ {n : ℕ} (hn₀ : 1 < n) (hprime : ¬n.Prime), n < a n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) ↔
    (∀ {n : ℕ} (hn₀ : 1 < n) (hprime : ¬n.Prime), n < a n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : ¬(n ≤ 1)) (hprime : ¬n.Prime), n < a n

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) ↔
    (∀ {n : ℕ} (hn : ¬(n ≤ 1)) (hprime : ¬n.Prime), n < a n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) ↔
    (∀ {n : ℕ} (hn : ¬(n ≤ 1)) (hprime : ¬n.Prime), n < a n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) ↔
    (∀ {n : ℕ} (hn : ¬(n ≤ 1)) (hprime : ¬n.Prime), n < a n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) ↔
    (∀ {n : ℕ} (hn : ¬(n ≤ 1)) (hprime : ¬n.Prime), n < a n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 2 ≤ n) (hprime : ¬n.Prime), n < a n

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 < n) ↔ (2 ≤ n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 < n) ↔ (2 ≤ n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 < n) ↔ (2 ≤ n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 < n) ↔ (2 ≤ n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 < n) ↔ (2 ≤ n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 < n) ↔ (2 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 < n) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 < n) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) ↔
    (∀ {n : ℕ} (hn : 2 ≤ n) (hprime : ¬n.Prime), n < a n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) ↔
    (∀ {n : ℕ} (hn : 2 ≤ n) (hprime : ¬n.Prime), n < a n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) ↔
    (∀ {n : ℕ} (hn : 2 ≤ n) (hprime : ¬n.Prime), n < a n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) ↔
    (∀ {n : ℕ} (hn : 2 ≤ n) (hprime : ¬n.Prime), n < a n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : n > 1) (hprime : ¬n.Prime), n ≤ a n

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : n > 1) (hprime : ¬n.Prime), n ≤ a n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : n > 1) (hprime : ¬n.Prime), n ≤ a n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : n > 1) (hprime : ¬n.Prime), n ≤ a n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : n > 1) (hprime : ¬n.Prime), n ≤ a n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : n > 1) (hprime : ¬n.Prime), n ≤ a n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : n > 1) (hprime : ¬n.Prime), n ≤ a n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : n > 1) (hprime : ¬n.Prime), n ≤ a n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (n ≤ a n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (n ≤ a n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (n ≤ a n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (n ≤ a n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (n ≤ a n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (n ≤ a n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : n > 1) (hprime : ¬n.Prime), n > a n

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n > 1) (hprime : ¬n.Prime), n > a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n > 1) (hprime : ¬n.Prime), n > a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n > 1) (hprime : ¬n.Prime), n > a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n > 1) (hprime : ¬n.Prime), n > a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n > 1) (hprime : ¬n.Prime), n > a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n > 1) (hprime : ¬n.Prime), n > a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n > 1) (hprime : ¬n.Prime), n > a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : n > 1) (hprime : ¬n.Prime), n > a n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : n > 1) (hprime : ¬n.Prime), n > a n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : n > 1) (hprime : ¬n.Prime), n > a n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : n > 1) (hprime : ¬n.Prime), n > a n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : n > 1) (hprime : ¬n.Prime), n > a n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : n > 1) (hprime : ¬n.Prime), n > a n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : n > 1) (hprime : ¬n.Prime), n > a n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬n.Prime) ∧ (¬(n > a n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬n.Prime) ∧ (¬(n > a n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬n.Prime) ∧ (¬(n > a n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬n.Prime) ∧ (¬(n > a n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬n.Prime) ∧ (¬(n > a n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬n.Prime) ∧ (¬(n > a n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (n > a n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (n > a n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (n > a n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (n > a n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (n > a n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (n > a n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), a n ≥ n

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), a n ≥ n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), a n ≥ n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), a n ≥ n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), a n ≥ n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), a n ≥ n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), a n ≥ n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), a n ≥ n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (a n ≥ n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (a n ≥ n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (a n ≥ n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (a n ≥ n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (a n ≥ n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (a n ≥ n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), a n < n

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), a n < n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), a n < n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), a n < n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), a n < n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), a n < n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), a n < n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), a n < n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), a n < n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), a n < n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), a n < n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), a n < n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), a n < n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), a n < n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), a n < n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬n.Prime) ∧ (¬(a n < n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬n.Prime) ∧ (¬(a n < n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬n.Prime) ∧ (¬(a n < n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬n.Prime) ∧ (¬(a n < n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬n.Prime) ∧ (¬(a n < n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬n.Prime) ∧ (¬(a n < n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (a n < n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (a n < n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (a n < n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (a n < n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (a n < n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (a n < n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 2 ≤ n) (hprime : ¬n.Prime), n ≤ a n

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : 2 ≤ n) (hprime : ¬n.Prime), n ≤ a n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : 2 ≤ n) (hprime : ¬n.Prime), n ≤ a n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : 2 ≤ n) (hprime : ¬n.Prime), n ≤ a n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : 2 ≤ n) (hprime : ¬n.Prime), n ≤ a n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : 2 ≤ n) (hprime : ¬n.Prime), n ≤ a n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : 2 ≤ n) (hprime : ¬n.Prime), n ≤ a n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : 2 ≤ n) (hprime : ¬n.Prime), n ≤ a n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (n ≤ a n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (n ≤ a n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (n ≤ a n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (n ≤ a n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (n ≤ a n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (n ≤ a n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 2 ≤ n) (hprime : ¬n.Prime), n > a n

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n) (hprime : ¬n.Prime), n > a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n) (hprime : ¬n.Prime), n > a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n) (hprime : ¬n.Prime), n > a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n) (hprime : ¬n.Prime), n > a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n) (hprime : ¬n.Prime), n > a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n) (hprime : ¬n.Prime), n > a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n) (hprime : ¬n.Prime), n > a n) →
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : 2 ≤ n) (hprime : ¬n.Prime), n > a n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : 2 ≤ n) (hprime : ¬n.Prime), n > a n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : 2 ≤ n) (hprime : ¬n.Prime), n > a n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : 2 ≤ n) (hprime : ¬n.Prime), n > a n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : 2 ≤ n) (hprime : ¬n.Prime), n > a n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : 2 ≤ n) (hprime : ¬n.Prime), n > a n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime), n < a n) →
    (∀ {n : ℕ} (hn : 2 ≤ n) (hprime : ¬n.Prime), n > a n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬n.Prime) ∧ (¬(n > a n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬n.Prime) ∧ (¬(n > a n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬n.Prime) ∧ (¬(n > a n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬n.Prime) ∧ (¬(n > a n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬n.Prime) ∧ (¬(n > a n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬n.Prime) ∧ (¬(n > a n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (n > a n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (n > a n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (n > a n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (n > a n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (n > a n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < a n) ↔ (n > a n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
