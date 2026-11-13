import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Ratio of product of GCDs to product of factorials of floor divisions

$$a(n) = \frac{\prod_{j=1}^n \prod_{k=1}^n \gcd(j,k)}{\prod_{k=1}^n (\lfloor n/k \rfloor!)^k}$$

*References:*
- [A129365](https://oeis.org/A129365)
-/

section

namespace OeisA129365

/-- $a(n) = \frac{\prod_{j=1}^n \prod_{k=1}^n \gcd(j,k)}{\prod_{k=1}^n (\lfloor n/k \rfloor!)^k}$. -/
def a (n : ℕ) : ℚ :=
  let num : ℚ := (Finset.Icc 1 n).prod fun j => (Finset.Icc 1 n).prod fun k => Nat.gcd j k
  let den : ℚ := (Finset.Icc 1 n).prod fun k => (n / k).factorial ^ k
  num / den

/-- Sequence A004125: sum of remainders $n \bmod k$ for $1 \le k \le n$. -/
def b (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, (n % k)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hn : 0 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) →
    (∀ (n p : ℕ) (hn : 0 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) →
    (∀ (n p : ℕ) (hn : 0 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) →
    (∀ (n p : ℕ) (hn : 0 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) →
    (∀ (n p : ℕ) (hn : 0 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) →
    (∀ (n p : ℕ) (hn : 0 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) →
    (∀ (n p : ℕ) (hn : 0 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) →
    (∀ (n p : ℕ) (hn : 0 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (0 < n) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (0 < n) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (0 < n) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hn : 0 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hn : n > 0) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (0 < n) ↔ (n > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (0 < n) ↔ (n > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (0 < n) ↔ (n > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (0 < n) ↔ (n > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (0 < n) ↔ (n > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (0 < n) ↔ (n > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (0 < n) ↔ (n > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (0 < n) ↔ (n > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hn : 0 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) ↔
    (∀ (n p : ℕ) (hn : n > 0) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hn : 0 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) ↔
    (∀ (n p : ℕ) (hn : n > 0) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hn : 0 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) ↔
    (∀ (n p : ℕ) (hn : n > 0) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hn : 0 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) ↔
    (∀ (n p : ℕ) (hn : n > 0) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hn : 0 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hp : p.Prime) (hn : 0 < n), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hn : 0 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) ↔
    (∀ (n p : ℕ) (hp : p.Prime) (hn : 0 < n), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hn : 0 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) ↔
    (∀ (n p : ℕ) (hp : p.Prime) (hn : 0 < n), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hn : 0 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) ↔
    (∀ (n p : ℕ) (hp : p.Prime) (hn : 0 < n), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hn : 0 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) ↔
    (∀ (n p : ℕ) (hp : p.Prime) (hn : 0 < n), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hn : 0 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hn₀ : 0 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hn : 0 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) ↔
    (∀ (n p : ℕ) (hn₀ : 0 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hn : 0 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) ↔
    (∀ (n p : ℕ) (hn₀ : 0 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hn : 0 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) ↔
    (∀ (n p : ℕ) (hn₀ : 0 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hn : 0 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) ↔
    (∀ (n p : ℕ) (hn₀ : 0 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hn : 0 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hn : ¬(n ≤ 0)) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hn : 0 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) ↔
    (∀ (n p : ℕ) (hn : ¬(n ≤ 0)) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hn : 0 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) ↔
    (∀ (n p : ℕ) (hn : ¬(n ≤ 0)) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hn : 0 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) ↔
    (∀ (n p : ℕ) (hn : ¬(n ≤ 0)) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hn : 0 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) ↔
    (∀ (n p : ℕ) (hn : ¬(n ≤ 0)) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hn : 0 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hn : 1 ≤ n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hn : 0 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) ↔
    (∀ (n p : ℕ) (hn : 1 ≤ n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hn : 0 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) ↔
    (∀ (n p : ℕ) (hn : 1 ≤ n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hn : 0 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) ↔
    (∀ (n p : ℕ) (hn : 1 ≤ n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hn : 0 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) ↔
    (∀ (n p : ℕ) (hn : 1 ≤ n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hn : 0 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hn : 1 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hn : 0 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) →
    (∀ (n p : ℕ) (hn : 1 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hn : 0 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) →
    (∀ (n p : ℕ) (hn : 1 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hn : 0 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) →
    (∀ (n p : ℕ) (hn : 1 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hn : 0 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) →
    (∀ (n p : ℕ) (hn : 1 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hn : 0 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) →
    (∀ (n p : ℕ) (hn : 1 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hn : 0 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) →
    (∀ (n p : ℕ) (hn : 1 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hn : 0 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) →
    (∀ (n p : ℕ) (hn : 1 < n) (hp : p.Prime), padicValRat p (a (n * p)) = ∑' i : ℕ, (b (n / p ^ i) : ℤ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (0 < n) ↔ (1 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (0 < n) ↔ (1 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (0 < n) ↔ (1 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hn : 0 < n) (hp : p.Prime) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hn : 0 < n) (hp : p.Prime) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hn : 0 < n) (hp : p.Prime) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hn : 0 < n) (hp : p.Prime) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hn : 0 < n) (hp : p.Prime) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
