import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Conjectures associated with A063880

A063880 lists numbers $n$ such that $\sigma(n) = 2 \cdot \text{usigma}(n)$, where $\sigma(n)$ is the
sum of all divisors and $\text{usigma}(n)$ is the sum of unitary divisors.

Equivalently, these are numbers whose unitary and non-unitary divisors have equal sum.

The conjectures state that all members satisfy $n \equiv 108 \pmod{216}$, and that all
primitive terms (those whose proper divisors aren't in the sequence) are powerful numbers,
with $108$ being the only primitive term.

*References:*
- [A063880](https://oeis.org/A063880)
-/

section

namespace OeisA63880

open scoped ArithmeticFunction.sigma

/-- The set of unitary divisors of $n$: divisors $d$ such that $\gcd(d, n/d) = 1$. -/
def unitaryDivisors (n : ℕ) : Finset ℕ :=
  {d ∈ n.divisors | d.Coprime (n / d)}

/-- The sum of unitary divisors of $n$, denoted $\text{usigma}(n)$. -/
def usigma (n : ℕ) : ℕ :=
  ∑ d ∈ unitaryDivisors n, d

/-- A number $n$ is in the sequence A063880 if $\sigma(n) = 2 \cdot \text{usigma}(n)$. -/
def A (n : ℕ) : Prop :=
  0 < n ∧ σ 1 n = 2 * usigma n

/-- A term $n$ is primitive if no proper divisor of $n$ is in the sequence. -/
abbrev IsPrimitiveTerm (n : ℕ) : Prop := {n | A n}.IsPrimitive n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m p : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)

set_option maxHeartbeats 200000 in
example :
    (∀ {m p : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) →
    (∀ {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m p : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) →
    (∀ {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m p : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) →
    (∀ {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {m p : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) →
    (∀ {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m p : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) →
    (∀ {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {m p : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) →
    (∀ {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {m p : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) →
    (∀ {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {m p : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) :
    (0 < m) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {m p : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) :
    (0 < m) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {m p : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) :
    (0 < m) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {m p : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) :
    (0 < m) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {m p : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) :
    (0 < m) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {m p : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) :
    (0 < m) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {m p : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) :
    (0 < m) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((0 < m) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((0 < m) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((0 < m) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((0 < m) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((0 < m) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((0 < m) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m p : ℕ} (hm : m > 0) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)

set_option maxHeartbeats 200000 in
example {m p : ℕ} :
    (0 < m) ↔ (m > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {m p : ℕ} :
    (0 < m) ↔ (m > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {m p : ℕ} :
    (0 < m) ↔ (m > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {m p : ℕ} :
    (0 < m) ↔ (m > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {m p : ℕ} :
    (0 < m) ↔ (m > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {m p : ℕ} :
    (0 < m) ↔ (m > 0) := by
  omega

set_option maxHeartbeats 200000 in
example {m p : ℕ} :
    (0 < m) ↔ (m > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {m p : ℕ} :
    (0 < m) ↔ (m > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) ↔
    (∀ {m p : ℕ} (hm : m > 0) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) ↔
    (∀ {m p : ℕ} (hm : m > 0) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) ↔
    (∀ {m p : ℕ} (hm : m > 0) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) ↔
    (∀ {m p : ℕ} (hm : m > 0) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m p : ℕ} (hp : p.Prime) (hm : 0 < m) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)

set_option maxHeartbeats 200000 in
example :
    (∀ {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) ↔
    (∀ {m p : ℕ} (hp : p.Prime) (hm : 0 < m) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) ↔
    (∀ {m p : ℕ} (hp : p.Prime) (hm : 0 < m) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) ↔
    (∀ {m p : ℕ} (hp : p.Prime) (hm : 0 < m) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) ↔
    (∀ {m p : ℕ} (hp : p.Prime) (hm : 0 < m) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m p : ℕ} (hm₀ : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)

set_option maxHeartbeats 200000 in
example :
    (∀ {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) ↔
    (∀ {m p : ℕ} (hm₀ : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) ↔
    (∀ {m p : ℕ} (hm₀ : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) ↔
    (∀ {m p : ℕ} (hm₀ : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) ↔
    (∀ {m p : ℕ} (hm₀ : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m p : ℕ} (hm : ¬(m ≤ 0)) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)

set_option maxHeartbeats 200000 in
example {m p : ℕ} :
    (0 < m) ↔ (¬(m ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {m p : ℕ} :
    (0 < m) ↔ (¬(m ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {m p : ℕ} :
    (0 < m) ↔ (¬(m ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {m p : ℕ} :
    (0 < m) ↔ (¬(m ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {m p : ℕ} :
    (0 < m) ↔ (¬(m ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {m p : ℕ} :
    (0 < m) ↔ (¬(m ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example {m p : ℕ} :
    (0 < m) ↔ (¬(m ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {m p : ℕ} :
    (0 < m) ↔ (¬(m ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) ↔
    (∀ {m p : ℕ} (hm : ¬(m ≤ 0)) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) ↔
    (∀ {m p : ℕ} (hm : ¬(m ≤ 0)) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) ↔
    (∀ {m p : ℕ} (hm : ¬(m ≤ 0)) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) ↔
    (∀ {m p : ℕ} (hm : ¬(m ≤ 0)) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m p : ℕ} (hm : 1 ≤ m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)

set_option maxHeartbeats 200000 in
example {m p : ℕ} :
    (0 < m) ↔ (1 ≤ m) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {m p : ℕ} :
    (0 < m) ↔ (1 ≤ m) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {m p : ℕ} :
    (0 < m) ↔ (1 ≤ m) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {m p : ℕ} :
    (0 < m) ↔ (1 ≤ m) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {m p : ℕ} :
    (0 < m) ↔ (1 ≤ m) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {m p : ℕ} :
    (0 < m) ↔ (1 ≤ m) := by
  omega

set_option maxHeartbeats 200000 in
example {m p : ℕ} :
    (0 < m) ↔ (1 ≤ m) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {m p : ℕ} :
    (0 < m) ↔ (1 ≤ m) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) ↔
    (∀ {m p : ℕ} (hm : 1 ≤ m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) ↔
    (∀ {m p : ℕ} (hm : 1 ≤ m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) ↔
    (∀ {m p : ℕ} (hm : 1 ≤ m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) ↔
    (∀ {m p : ℕ} (hm : 1 ≤ m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m p : ℕ} (hm : 1 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)

set_option maxHeartbeats 200000 in
example :
    (∀ {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) →
    (∀ {m p : ℕ} (hm : 1 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) →
    (∀ {m p : ℕ} (hm : 1 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) →
    (∀ {m p : ℕ} (hm : 1 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) →
    (∀ {m p : ℕ} (hm : 1 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) →
    (∀ {m p : ℕ} (hm : 1 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) →
    (∀ {m p : ℕ} (hm : 1 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) →
    (∀ {m p : ℕ} (hm : 1 < m) (hp : p.Prime) (hpm : ¬ p ∣ m), unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {m p : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) :
    (0 < m) ↔ (1 < m) := by
  omega

set_option maxHeartbeats 200000 in
example {m p : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) :
    (0 < m) ↔ (1 < m) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {m p : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) :
    (0 < m) ↔ (1 < m) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {m p : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) :
    (0 < m) ↔ (1 < m) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {m p : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) :
    (0 < m) ↔ (1 < m) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {m p : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) :
    (0 < m) ↔ (1 < m) := by
  simp_all

set_option maxHeartbeats 200000 in
example {m p : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) :
    (0 < m) ↔ (1 < m) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (p : ℕ), (p.Prime) ∧ (¬ p ∣ m) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((0 < m) ↔ (1 < m)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((0 < m) ↔ (1 < m)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((0 < m) ↔ (1 < m)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((0 < m) ↔ (1 < m)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((0 < m) ↔ (1 < m)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((0 < m) ↔ (1 < m)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
