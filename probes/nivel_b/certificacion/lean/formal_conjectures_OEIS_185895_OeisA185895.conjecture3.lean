import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Coefficients of $\prod_{k>0} (1 - x^k/k!)$

The sequence $a(n)$ has exponential generating function
$$E(x) = \prod_{k=1}^\infty \left(1 - \frac{x^k}{k!}\right),$$
so that $a(n) = n! [x^n] \prod_{k=1}^n \left(1 - \frac{x^k}{k!}\right)$.

*References:*
- [A185895](https://oeis.org/A185895)
-/

section

open Polynomial

namespace OeisA185895

/-- The finite polynomial approximation $\prod_{k=1}^n (1 - X^k / k!)$. -/
noncomputable def P (n : ℕ) : Polynomial ℚ :=
  ∏ k ∈ Finset.Icc 1 n, (1 - C (1 / (k.factorial : ℚ)) * X ^ k)

/-- The sequence $a(n) = n! [x^n] \prod_{k=1}^n (1 - x^k / k!)$. -/
noncomputable def a (n : ℕ) : ℤ :=
  if n = 0 then 1
  else (coeff (P n) n * (n.factorial : ℚ)).floor

/-- A natural number $n$ is triangular if $n = k(k+1)/2$ for some $k \in \mathbb{N}$. -/
def IsTriangular (n : ℕ) : Prop := ∃ k : ℕ, n = k * (k + 1) / 2

/-- The $n$-th coefficient of the square of the ordinary generating function $A(x)^2$. -/
noncomputable def c (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), a k * a (n - k)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) →
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) →
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) →
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) →
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) →
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) →
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) →
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (0 < n) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (0 < n) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (0 < n) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(3 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

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
  ∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : n > 0) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) :
    (0 < n) ↔ (n > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) :
    (0 < n) ↔ (n > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) :
    (0 < n) ↔ (n > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) :
    (0 < n) ↔ (n > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) :
    (0 < n) ↔ (n > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) :
    (0 < n) ↔ (n > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) :
    (0 < n) ↔ (n > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) :
    (0 < n) ↔ (n > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) ↔
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : n > 0) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) ↔
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : n > 0) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) ↔
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : n > 0) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) ↔
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : n > 0) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hk : 0 < k) (hn : 0 < n), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) ↔
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hk : 0 < k) (hn : 0 < n), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) ↔
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hk : 0 < k) (hn : 0 < n), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) ↔
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hk : 0 < k) (hn : 0 < n), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) ↔
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hk : 0 < k) (hn : 0 < n), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp₀ : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) ↔
    (∀ (p : ℕ) (hp₀ : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) ↔
    (∀ (p : ℕ) (hp₀ : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) ↔
    (∀ (p : ℕ) (hp₀ : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) ↔
    (∀ (p : ℕ) (hp₀ : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : ¬(n ≤ 0)) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) ↔
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : ¬(n ≤ 0)) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) ↔
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : ¬(n ≤ 0)) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) ↔
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : ¬(n ≤ 0)) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) ↔
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : ¬(n ≤ 0)) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 1 ≤ n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) ↔
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 1 ≤ n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) ↔
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 1 ≤ n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) ↔
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 1 ≤ n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) ↔
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 1 ≤ n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 1 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) →
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 1 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) →
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 1 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) →
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 1 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) →
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 1 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) →
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 1 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) →
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 1 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) →
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 1 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (0 < n) ↔ (1 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (0 < n) ↔ (1 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (0 < n) ↔ (1 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(3 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(2 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(2 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

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
example : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) →
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) →
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) →
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) →
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) →
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) →
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) →
    (∀ (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k), a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k]) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) (hp : p.Prime) (hn : 0 < n) :
    (0 < k) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) (hp : p.Prime) (hn : 0 < n) :
    (0 < k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) (hp : p.Prime) (hn : 0 < n) :
    (0 < k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) (hp : p.Prime) (hn : 0 < n) :
    (0 < k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) (hp : p.Prime) (hn : 0 < n) :
    (0 < k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) (hp : p.Prime) (hn : 0 < n) :
    (0 < k) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) (hp : p.Prime) (hn : 0 < n) :
    (0 < k) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < n) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < n) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < n) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < n) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < n) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < n) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < n) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < n) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < n) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < n) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < n) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < n) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < n) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < n) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < n) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < n) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < n) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < n) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < n) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < n) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(3 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < n) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < n) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < n) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < n) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < n) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < n) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < n) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < n) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < n) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < n) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < n) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (n : ℕ) (k : ℕ), (p.Prime) ∧ (0 < n) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) (hp : p.Prime) (hn : 0 < n) (hk : 0 < k) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) (hp : p.Prime) (hn : 0 < n) (hk : 0 < k) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) (hp : p.Prime) (hn : 0 < n) (hk : 0 < k) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) (hp : p.Prime) (hn : 0 < n) (hk : 0 < k) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (p : ℕ) (n k : ℕ) (hp : p.Prime) (hn : 0 < n) (hk : 0 < k) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
