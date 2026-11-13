import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Numerator of a sum involving binomial coefficients

$a(n)$ is the numerator of
$\sum_{k = 1}^n \frac{1}{k^3} \binom{n}{k}^2 \binom{n+k}{k}^2$ for $n \ge 1$
with $a(0) = 0$.

*References:*
- [A357513](https://oeis.org/A357513)
-/

section
namespace OeisA357513

open Nat

/--
A357513: $a(n) = \text{numerator of }
\sum_{k = 1..n} \frac{1}{k^3} \binom{n}{k}^2 \binom{n+k}{k}^2
\text{ for } n \ge 1 \text{ with } a(0) = 0$.
-/
def a (n : ℕ) : ℕ :=
 ∑ k ∈ (Finset.Icc 1 n), ((n.choose k : ℚ) ^ 2 * ((n + k).choose k : ℚ) ^ 2) / k ^ 3 |>.num.natAbs

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7) :
    (p ≥ 3) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7) :
    (p ≥ 3) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7) :
    (p ≥ 3) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7) :
    (p ≥ 3) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7) :
    (p ≥ 3) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7) :
    (p ≥ 3) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7) :
    (p ≥ 3) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (True))) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (True))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (True))) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (True))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (True))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (True))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (True))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (True))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (True))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (True))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≥ 3) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≥ 3) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≥ 3) ↔ (True)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≥ 3) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≥ 3) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≥ 3) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≥ 3) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p > 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p > 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p > 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p > 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p > 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p > 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p > 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p > 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7) :
    (p ≥ 3) ↔ (p > 3) := by
  omega

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7) :
    (p ≥ 3) ↔ (p > 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7) :
    (p ≥ 3) ↔ (p > 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7) :
    (p ≥ 3) ↔ (p > 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7) :
    (p ≥ 3) ↔ (p > 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7) :
    (p ≥ 3) ↔ (p > 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7) :
    (p ≥ 3) ↔ (p > 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (p > 3))) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (p > 3))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (p > 3))) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (p > 3))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (p > 3))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (p > 3))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (p > 3))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (p > 3))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (p > 3))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (p > 3))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≥ 3) ↔ (p > 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≥ 3) ↔ (p > 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≥ 3) ↔ (p > 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≥ 3) ↔ (p > 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≥ 3) ↔ (p > 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≥ 3) ↔ (p > 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≥ 3) ↔ (p > 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 4) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 4) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 4) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 4) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 4) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 4) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 4) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 4) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7) :
    (p ≥ 3) ↔ (p ≥ 4) := by
  omega

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7) :
    (p ≥ 3) ↔ (p ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7) :
    (p ≥ 3) ↔ (p ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7) :
    (p ≥ 3) ↔ (p ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7) :
    (p ≥ 3) ↔ (p ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7) :
    (p ≥ 3) ↔ (p ≥ 4) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7) :
    (p ≥ 3) ↔ (p ≥ 4) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (p ≥ 4))) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (p ≥ 4))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (p ≥ 4))) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (p ≥ 4))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (p ≥ 4))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (p ≥ 4))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (p ≥ 4))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (p ≥ 4))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (p ≥ 4))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (p ≥ 4))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≥ 3) ↔ (p ≥ 4)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≥ 3) ↔ (p ≥ 4)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≥ 3) ↔ (p ≥ 4)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≥ 3) ↔ (p ≥ 4)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≥ 3) ↔ (p ≥ 4)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≥ 3) ↔ (p ≥ 4)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≥ 3) ↔ (p ≥ 4)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (h_ge3 : 3 ≤ p) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p ≥ 3) ↔ (3 ≤ p) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p ≥ 3) ↔ (3 ≤ p) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p ≥ 3) ↔ (3 ≤ p) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p ≥ 3) ↔ (3 ≤ p) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p ≥ 3) ↔ (3 ≤ p) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p ≥ 3) ↔ (3 ≤ p) := by
  omega

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p ≥ 3) ↔ (3 ≤ p) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p ≥ 3) ↔ (3 ≤ p) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) ↔
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : 3 ≤ p) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) ↔
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : 3 ≤ p) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) ↔
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : 3 ≤ p) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) ↔
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : 3 ≤ p) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : ¬(p = 7)), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p ≠ 7) ↔ (¬(p = 7)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p ≠ 7) ↔ (¬(p = 7)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p ≠ 7) ↔ (¬(p = 7)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p ≠ 7) ↔ (¬(p = 7)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p ≠ 7) ↔ (¬(p = 7)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p ≠ 7) ↔ (¬(p = 7)) := by
  omega

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p ≠ 7) ↔ (¬(p = 7)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p ≠ 7) ↔ (¬(p = 7)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) ↔
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : ¬(p = 7)), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) ↔
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : ¬(p = 7)), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) ↔
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : ¬(p = 7)), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) ↔
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : ¬(p = 7)), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (h_ge3 : p ≥ 3) (hp : p.Prime) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) ↔
    (∀ (p : ℕ) (h_ge3 : p ≥ 3) (hp : p.Prime) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) ↔
    (∀ (p : ℕ) (h_ge3 : p ≥ 3) (hp : p.Prime) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) ↔
    (∀ (p : ℕ) (h_ge3 : p ≥ 3) (hp : p.Prime) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) ↔
    (∀ (p : ℕ) (h_ge3 : p ≥ 3) (hp : p.Prime) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp₀ : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) ↔
    (∀ (p : ℕ) (hp₀ : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) ↔
    (∀ (p : ℕ) (hp₀ : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) ↔
    (∀ (p : ℕ) (hp₀ : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) ↔
    (∀ (p : ℕ) (hp₀ : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (h_ge3 : ¬(p < 3)) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p ≥ 3) ↔ (¬(p < 3)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p ≥ 3) ↔ (¬(p < 3)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p ≥ 3) ↔ (¬(p < 3)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p ≥ 3) ↔ (¬(p < 3)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p ≥ 3) ↔ (¬(p < 3)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p ≥ 3) ↔ (¬(p < 3)) := by
  omega

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p ≥ 3) ↔ (¬(p < 3)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p ≥ 3) ↔ (¬(p < 3)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) ↔
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : ¬(p < 3)) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) ↔
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : ¬(p < 3)) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) ↔
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : ¬(p < 3)) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) ↔
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : ¬(p < 3)) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p > 2) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p ≥ 3) ↔ (p > 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p ≥ 3) ↔ (p > 2) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p ≥ 3) ↔ (p > 2) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p ≥ 3) ↔ (p > 2) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p ≥ 3) ↔ (p > 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p ≥ 3) ↔ (p > 2) := by
  omega

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p ≥ 3) ↔ (p > 2) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p ≥ 3) ↔ (p > 2) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) ↔
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p > 2) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) ↔
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p > 2) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) ↔
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p > 2) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) ↔
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p > 2) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (h_ge3 : 3 < p) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : 3 < p) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : 3 < p) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : 3 < p) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : 3 < p) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : 3 < p) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : 3 < p) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : 3 < p) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7) :
    (p ≥ 3) ↔ (3 < p) := by
  omega

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7) :
    (p ≥ 3) ↔ (3 < p) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7) :
    (p ≥ 3) ↔ (3 < p) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7) :
    (p ≥ 3) ↔ (3 < p) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7) :
    (p ≥ 3) ↔ (3 < p) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7) :
    (p ≥ 3) ↔ (3 < p) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7) :
    (p ≥ 3) ↔ (3 < p) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (3 < p))) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (3 < p))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (3 < p))) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (3 < p))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (3 < p))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (3 < p))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (3 < p))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (3 < p))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (3 < p))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (3 < p))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≥ 3) ↔ (3 < p)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≥ 3) ↔ (3 < p)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≥ 3) ↔ (3 < p)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≥ 3) ↔ (3 < p)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≥ 3) ↔ (3 < p)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≥ 3) ↔ (3 < p)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≥ 3) ↔ (3 < p)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (h_ge3 : 4 ≤ p) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : 4 ≤ p) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : 4 ≤ p) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : 4 ≤ p) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : 4 ≤ p) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : 4 ≤ p) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : 4 ≤ p) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : 4 ≤ p) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7) :
    (p ≥ 3) ↔ (4 ≤ p) := by
  omega

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7) :
    (p ≥ 3) ↔ (4 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7) :
    (p ≥ 3) ↔ (4 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7) :
    (p ≥ 3) ↔ (4 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7) :
    (p ≥ 3) ↔ (4 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7) :
    (p ≥ 3) ↔ (4 ≤ p) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7) :
    (p ≥ 3) ↔ (4 ≤ p) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (4 ≤ p))) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (4 ≤ p))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (4 ≤ p))) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (4 ≤ p))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (4 ≤ p))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (4 ≤ p))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (4 ≤ p))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (4 ≤ p))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (4 ≤ p))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (4 ≤ p))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≥ 3) ↔ (4 ≤ p)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≥ 3) ↔ (4 ≤ p)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≥ 3) ↔ (4 ≤ p)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≥ 3) ↔ (4 ≤ p)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≥ 3) ↔ (4 ≤ p)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≥ 3) ↔ (4 ≤ p)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≥ 3) ↔ (4 ≤ p)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 2) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 2) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 2) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 2) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 2) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 2) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 2) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 2) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7) :
    (p ≥ 3) ↔ (p ≥ 2) := by
  omega

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7) :
    (p ≥ 3) ↔ (p ≥ 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7) :
    (p ≥ 3) ↔ (p ≥ 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7) :
    (p ≥ 3) ↔ (p ≥ 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7) :
    (p ≥ 3) ↔ (p ≥ 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7) :
    (p ≥ 3) ↔ (p ≥ 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_neq7 : p ≠ 7) :
    (p ≥ 3) ↔ (p ≥ 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (p ≥ 2))) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (p ≥ 2))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (p ≥ 2))) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (p ≥ 2))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (p ≥ 2))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (p ≥ 2))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (p ≥ 2))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (p ≥ 2))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (p ≥ 2))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≠ 7) ∧ (¬((p ≥ 3) ↔ (p ≥ 2))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≥ 3) ↔ (p ≥ 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≥ 3) ↔ (p ≥ 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≥ 3) ↔ (p ≥ 2)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≥ 3) ↔ (p ≥ 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≥ 3) ↔ (p ≥ 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≥ 3) ↔ (p ≥ 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≥ 3) ↔ (p ≥ 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p > 2) (h_neq7 : p ≠ 8), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p > 2) (h_neq7 : p ≠ 8), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p > 2) (h_neq7 : p ≠ 8), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p > 2) (h_neq7 : p ≠ 8), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p > 2) (h_neq7 : p ≠ 8), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p > 2) (h_neq7 : p ≠ 8), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p > 2) (h_neq7 : p ≠ 8), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p > 2) (h_neq7 : p ≠ 8), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p > 2) (h_neq7 : p ≠ 8), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p > 2) (h_neq7 : p ≠ 8), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p > 2) (h_neq7 : p ≠ 8), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p > 2) (h_neq7 : p ≠ 8), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p > 2) (h_neq7 : p ≠ 8), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p > 2) (h_neq7 : p ≠ 8), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) →
    (∀ (p : ℕ) (hp : p.Prime) (h_ge3 : p > 2) (h_neq7 : p ≠ 8), (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4]) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) :
    (p ≠ 7) ↔ (p ≠ 8) := by
  omega

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) :
    (p ≠ 7) ↔ (p ≠ 8) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) :
    (p ≠ 7) ↔ (p ≠ 8) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) :
    (p ≠ 7) ↔ (p ≠ 8) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) :
    (p ≠ 7) ↔ (p ≠ 8) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) :
    (p ≠ 7) ↔ (p ≠ 8) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) :
    (p ≠ 7) ↔ (p ≠ 8) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≥ 3) ∧ (¬((p ≠ 7) ↔ (p ≠ 8))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≥ 3) ∧ (¬((p ≠ 7) ↔ (p ≠ 8))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≥ 3) ∧ (¬((p ≠ 7) ↔ (p ≠ 8))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≥ 3) ∧ (¬((p ≠ 7) ↔ (p ≠ 8))) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≥ 3) ∧ (¬((p ≠ 7) ↔ (p ≠ 8))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≥ 3) ∧ (¬((p ≠ 7) ↔ (p ≠ 8))) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≥ 3) ∧ (¬((p ≠ 7) ↔ (p ≠ 8))) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≥ 3) ∧ (¬((p ≠ 7) ↔ (p ≠ 8))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≥ 3) ∧ (¬((p ≠ 7) ↔ (p ≠ 8))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≥ 3) ∧ (¬((p ≠ 7) ↔ (p ≠ 8))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p.Prime) ∧ (p ≥ 3) ∧ (¬((p ≠ 7) ↔ (p ≠ 8))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≠ 7) ↔ (p ≠ 8)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≠ 7) ↔ (p ≠ 8)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≠ 7) ↔ (p ≠ 8)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≠ 7) ↔ (p ≠ 8)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≠ 7) ↔ (p ≠ 8)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≠ 7) ↔ (p ≠ 8)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≠ 7) ↔ (p ≠ 8)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≠ 7) ↔ (p ≠ 8)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≠ 7) ↔ (p ≠ 8)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p ≠ 7) ↔ (p ≠ 8)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : p.Prime) (h_ge3 : p ≥ 3) (h_neq7 : p ≠ 7) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
