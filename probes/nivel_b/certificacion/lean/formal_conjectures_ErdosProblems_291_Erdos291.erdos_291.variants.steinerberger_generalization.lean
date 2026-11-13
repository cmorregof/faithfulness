import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 291

*References:*
- [erdosproblems.com/291](https://www.erdosproblems.com/291)
- [ErGr80, p.34] Erdős, P. and Graham, R., Old and new problems and results in combinatorial number
  theory. Monographies de L'Enseignement Mathematique (1980).
- [Sh16] P. Shiu, The denominators of harmonic numbers. arXiv:1607.02863 (2016).
- [WuYa22] Wu, Bing-Ling and Yan, Xiao-Hui, On the denominators of harmonic numbers. {IV}. C. R.
  Math. Acad. Sci. Paris (2022), 53--57.
-/

section

open Nat Finset Set Filter

namespace Erdos291

/--
$L_n$ is the least common multiple of $\{1,\ldots,n\}$.
-/
def L (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).lcm (fun x ↦ x)

/--
$a_n$ is defined by $\sum_{1\leq k\leq n}\frac{1}{k}=\frac{a_n}{L_n}$.
-/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, L n / k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hp : p.Prime), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) →
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) →
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) →
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) →
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) →
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) →
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) →
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (p ≤ n) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (p ≤ n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (p ≤ n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (p ≤ n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (p ≤ n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (p ≤ n) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (p ≤ n) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (True))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (True))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (True))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (True))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (True))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (True))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (True))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (True))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (True))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (True))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (True))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (True))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (True))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (True))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (True))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (True))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (True))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (True))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (True))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (True)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (True)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (True)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (True)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (True)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (True)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (True)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (True)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (True)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (True)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (True)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (True)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (True)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (True)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (True)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (True)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (True)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (True)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (True)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (True)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (True)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (True)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (True)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (True)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (True)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (True)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (True)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (True)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (True)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (True)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (True)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (True)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hp : p.Prime) (hpn : p < n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) →
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : p < n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) →
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : p < n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) →
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : p < n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) →
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : p < n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) →
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : p < n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) →
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : p < n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) →
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : p < n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (p ≤ n) ↔ (p < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (p ≤ n) ↔ (p < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (p ≤ n) ↔ (p < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (p ≤ n) ↔ (p < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (p ≤ n) ↔ (p < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (p ≤ n) ↔ (p < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (p ≤ n) ↔ (p < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (p < n))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (p < n))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (p < n))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (p < n))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (p < n))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (p < n))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (p < n))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (p < n))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (p < n))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (p < n))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (p < n))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (p < n))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (p < n))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (p < n))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (p < n))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (p < n))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (p < n))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (p < n))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (p < n))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (p < n))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (p < n))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (p < n))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (p < n))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (p < n))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (p < n))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (p < n))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (p < n))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (p < n))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (p < n))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (p < n))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (p < n))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (p < n))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (p < n)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (p < n)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (p < n)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (p < n)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (p < n)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (p < n)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (p < n)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (p < n)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (p < n)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (p < n)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (p < n)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (p < n)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (p < n)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (p < n)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (p < n)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (p < n)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (p < n)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (p < n)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (p < n)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (p < n)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (p < n)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (p < n)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (p < n)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (p < n)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (p < n)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (p < n)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (p < n)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (p < n)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (p < n)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (p < n)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (p < n)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (p < n)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hp : p.Prime) (hpn : n ≥ p), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (p ≤ n) ↔ (n ≥ p) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (p ≤ n) ↔ (n ≥ p) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (p ≤ n) ↔ (n ≥ p) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (p ≤ n) ↔ (n ≥ p) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (p ≤ n) ↔ (n ≥ p) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (p ≤ n) ↔ (n ≥ p) := by
  omega

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (p ≤ n) ↔ (n ≥ p) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (p ≤ n) ↔ (n ≥ p) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) ↔
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : n ≥ p), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) ↔
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : n ≥ p), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) ↔
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : n ≥ p), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) ↔
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : n ≥ p), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hpn : p ≤ n) (hp : p.Prime), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) ↔
    (∀ (n p : ℕ) (hpn : p ≤ n) (hp : p.Prime), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) ↔
    (∀ (n p : ℕ) (hpn : p ≤ n) (hp : p.Prime), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) ↔
    (∀ (n p : ℕ) (hpn : p ≤ n) (hp : p.Prime), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) ↔
    (∀ (n p : ℕ) (hpn : p ≤ n) (hp : p.Prime), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hp₀ : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) ↔
    (∀ (n p : ℕ) (hp₀ : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) ↔
    (∀ (n p : ℕ) (hp₀ : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) ↔
    (∀ (n p : ℕ) (hp₀ : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) ↔
    (∀ (n p : ℕ) (hp₀ : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hp : p.Prime) (hpn : ¬(n < p)), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (p ≤ n) ↔ (¬(n < p)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (p ≤ n) ↔ (¬(n < p)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (p ≤ n) ↔ (¬(n < p)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (p ≤ n) ↔ (¬(n < p)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (p ≤ n) ↔ (¬(n < p)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (p ≤ n) ↔ (¬(n < p)) := by
  omega

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (p ≤ n) ↔ (¬(n < p)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (p ≤ n) ↔ (¬(n < p)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) ↔
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : ¬(n < p)), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) ↔
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : ¬(n < p)), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) ↔
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : ¬(n < p)), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) ↔
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : ¬(n < p)), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hp : p.Prime) (hpn : n > p), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) →
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : n > p), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) →
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : n > p), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) →
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : n > p), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) →
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : n > p), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) →
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : n > p), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) →
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : n > p), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) →
    (∀ (n p : ℕ) (hp : p.Prime) (hpn : n > p), let k := n / p ^ Nat.log p n;
    p ∣ Nat.gcd (a n) (L n) ↔ (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (p ≤ n) ↔ (n > p) := by
  omega

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (p ≤ n) ↔ (n > p) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (p ≤ n) ↔ (n > p) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (p ≤ n) ↔ (n > p) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (p ≤ n) ↔ (n > p) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (p ≤ n) ↔ (n > p) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (p ≤ n) ↔ (n > p) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (n > p))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (n > p))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (n > p))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (n > p))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (n > p))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (n > p))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (n > p))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (n > p))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (n > p))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (n > p))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (n > p))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (n > p))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (n > p))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (n > p))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (n > p))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (n > p))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (n > p))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (n > p))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (n > p))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (n > p))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (n > p))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (n > p))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (n > p))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (n > p))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (n > p))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (n > p))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (n > p))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (n > p))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (n > p))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (n > p))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (n > p))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((p ≤ n) ↔ (n > p))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (n > p)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (n > p)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (n > p)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (n > p)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (n > p)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (n > p)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (n > p)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (n > p)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (n > p)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (n > p)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (n > p)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (n > p)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (n > p)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (n > p)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (n > p)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (n > p)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (n > p)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (n > p)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (n > p)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (n > p)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (n > p)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (n > p)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (n > p)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (n > p)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (n > p)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (n > p)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (n > p)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (n > p)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (n > p)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (n > p)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (n > p)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((p ≤ n) ↔ (n > p)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
