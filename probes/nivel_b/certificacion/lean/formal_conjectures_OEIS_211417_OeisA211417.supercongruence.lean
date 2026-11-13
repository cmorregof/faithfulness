import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Integrality and supercongruences of the factorial ratio $\frac{(6n)! n!}{(3n)! (2n)!^2}$

Integral factorial ratio sequence:
$$a(n) = \frac{(30n)! n!}{(15n)! (10n)! (6n)!}$$

*References:*
- [A211417](https://oeis.org/A211417)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
- [Me11] R. Meštrović, *Wolstenholme's theorem: Its Generalizations and Extensions in the last
  hundred and fifty years (1862-2012)*, [arXiv:1111.3057](https://arxiv.org/abs/1111.3057) (2011).
-/

section

namespace OeisA211417

/--
Integral factorial ratio sequence:
$$a(n) = \frac{(30n)! n!}{(15n)! (10n)! (6n)!}$$
-/
def a (n : ℕ) : ℕ :=
  (Nat.factorial (30 * n) * Nat.factorial n) /
  (Nat.factorial (15 * n) * Nat.factorial (10 * n) * Nat.factorial (6 * n))

open Nat Int Finset
def coprimeIndices (r : ℕ) : Finset ℕ :=
  (Finset.range (r + 1)).filter (fun i => 1 ≤ i ∧ Nat.gcd i 30 = 1)

/--
The product term in the denominator of the general conjecture:
$$\prod_{i = 1..r, i \text{ coprime to } 30} (30n - i)$$
We define this in ℤ to handle the $n=0$ case where $30n-i$ in the product might be negative.
-/
def divisorProduct (n r : ℕ) : ℤ :=
  (coprimeIndices r).prod (fun i : ℕ => 30 * (n : ℤ) - (i : ℤ))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p k : ℕ) (hp : p.Prime) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) →
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) →
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) →
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) →
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) →
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) →
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) →
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (5 ≤ p) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (5 ≤ p) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (5 ≤ p) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (5 ≤ p) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (5 ≤ p) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (5 ≤ p) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (5 ≤ p) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(0 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(6 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(1 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(5 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(4 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(6 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(5 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(6 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(4 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (True)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (True)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 < p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) →
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 < p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) →
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 < p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) →
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 < p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) →
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 < p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) →
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 < p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) →
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 < p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) →
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 < p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (5 ≤ p) ↔ (5 < p) := by
  omega

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (5 ≤ p) ↔ (5 < p) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (5 ≤ p) ↔ (5 < p) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (5 ≤ p) ↔ (5 < p) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (5 ≤ p) ↔ (5 < p) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (5 ≤ p) ↔ (5 < p) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (5 ≤ p) ↔ (5 < p) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(6 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(1 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(5 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(4 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(6 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(5 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(6 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(4 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (5 < p)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (5 < p)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (5 < p)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (5 < p)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (5 < p)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (5 < p)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (5 < p)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (5 < p)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p k : ℕ) (hp : p.Prime) (hp5 : 6 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) →
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 6 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) →
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 6 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) →
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 6 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) →
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 6 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) →
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 6 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) →
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 6 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) →
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 6 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (5 ≤ p) ↔ (6 ≤ p) := by
  omega

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (5 ≤ p) ↔ (6 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (5 ≤ p) ↔ (6 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (5 ≤ p) ↔ (6 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (5 ≤ p) ↔ (6 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (5 ≤ p) ↔ (6 ≤ p) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (5 ≤ p) ↔ (6 ≤ p) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(6 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(5 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(4 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(6 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(7 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(5 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(6 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(7 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(5 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(4 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (6 ≤ p)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (6 ≤ p)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (6 ≤ p)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (6 ≤ p)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (6 ≤ p)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (6 ≤ p)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (6 ≤ p)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (6 ≤ p)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (6 ≤ p)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p k : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))

set_option maxHeartbeats 200000 in
example (p k : ℕ) :
    (5 ≤ p) ↔ (p ≥ 5) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (p k : ℕ) :
    (5 ≤ p) ↔ (p ≥ 5) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (p k : ℕ) :
    (5 ≤ p) ↔ (p ≥ 5) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (p k : ℕ) :
    (5 ≤ p) ↔ (p ≥ 5) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (p k : ℕ) :
    (5 ≤ p) ↔ (p ≥ 5) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (p k : ℕ) :
    (5 ≤ p) ↔ (p ≥ 5) := by
  omega

set_option maxHeartbeats 200000 in
example (p k : ℕ) :
    (5 ≤ p) ↔ (p ≥ 5) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (p k : ℕ) :
    (5 ≤ p) ↔ (p ≥ 5) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) ↔
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) ↔
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) ↔
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) ↔
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p k : ℕ) (hp5 : 5 ≤ p) (hp : p.Prime) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) ↔
    (∀ (p k : ℕ) (hp5 : 5 ≤ p) (hp : p.Prime) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) ↔
    (∀ (p k : ℕ) (hp5 : 5 ≤ p) (hp : p.Prime) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) ↔
    (∀ (p k : ℕ) (hp5 : 5 ≤ p) (hp : p.Prime) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) ↔
    (∀ (p k : ℕ) (hp5 : 5 ≤ p) (hp : p.Prime) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p k : ℕ) (hp₀ : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) ↔
    (∀ (p k : ℕ) (hp₀ : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) ↔
    (∀ (p k : ℕ) (hp₀ : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) ↔
    (∀ (p k : ℕ) (hp₀ : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) ↔
    (∀ (p k : ℕ) (hp₀ : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p k : ℕ) (hp : p.Prime) (hp5 : ¬(p < 5)) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))

set_option maxHeartbeats 200000 in
example (p k : ℕ) :
    (5 ≤ p) ↔ (¬(p < 5)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (p k : ℕ) :
    (5 ≤ p) ↔ (¬(p < 5)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (p k : ℕ) :
    (5 ≤ p) ↔ (¬(p < 5)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (p k : ℕ) :
    (5 ≤ p) ↔ (¬(p < 5)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (p k : ℕ) :
    (5 ≤ p) ↔ (¬(p < 5)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (p k : ℕ) :
    (5 ≤ p) ↔ (¬(p < 5)) := by
  omega

set_option maxHeartbeats 200000 in
example (p k : ℕ) :
    (5 ≤ p) ↔ (¬(p < 5)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (p k : ℕ) :
    (5 ≤ p) ↔ (¬(p < 5)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) ↔
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : ¬(p < 5)) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) ↔
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : ¬(p < 5)) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) ↔
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : ¬(p < 5)) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) ↔
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : ¬(p < 5)) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p k : ℕ) (hp : p.Prime) (hp5 : 4 < p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))

set_option maxHeartbeats 200000 in
example (p k : ℕ) :
    (5 ≤ p) ↔ (4 < p) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (p k : ℕ) :
    (5 ≤ p) ↔ (4 < p) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (p k : ℕ) :
    (5 ≤ p) ↔ (4 < p) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (p k : ℕ) :
    (5 ≤ p) ↔ (4 < p) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (p k : ℕ) :
    (5 ≤ p) ↔ (4 < p) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (p k : ℕ) :
    (5 ≤ p) ↔ (4 < p) := by
  omega

set_option maxHeartbeats 200000 in
example (p k : ℕ) :
    (5 ≤ p) ↔ (4 < p) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (p k : ℕ) :
    (5 ≤ p) ↔ (4 < p) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) ↔
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 4 < p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) ↔
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 4 < p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) ↔
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 4 < p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) ↔
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 4 < p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p k : ℕ) (hp : p.Prime) (hp5 : p > 5) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) →
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : p > 5) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) →
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : p > 5) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) →
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : p > 5) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) →
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : p > 5) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) →
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : p > 5) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) →
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : p > 5) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) →
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : p > 5) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (5 ≤ p) ↔ (p > 5) := by
  omega

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (5 ≤ p) ↔ (p > 5) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (5 ≤ p) ↔ (p > 5) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (5 ≤ p) ↔ (p > 5) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (5 ≤ p) ↔ (p > 5) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (5 ≤ p) ↔ (p > 5) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (5 ≤ p) ↔ (p > 5) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(0 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(6 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(1 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(5 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(4 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(6 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(5 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(6 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(4 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (p > 5)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (p > 5)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (p > 5)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (p > 5)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (p > 5)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (p > 5)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (p > 5)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (p > 5)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p k : ℕ) (hp : p.Prime) (hp5 : p ≥ 6) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) →
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : p ≥ 6) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) →
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : p ≥ 6) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) →
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : p ≥ 6) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) →
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : p ≥ 6) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) →
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : p ≥ 6) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) →
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : p ≥ 6) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) →
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : p ≥ 6) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (5 ≤ p) ↔ (p ≥ 6) := by
  omega

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (5 ≤ p) ↔ (p ≥ 6) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (5 ≤ p) ↔ (p ≥ 6) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (5 ≤ p) ↔ (p ≥ 6) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (5 ≤ p) ↔ (p ≥ 6) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (5 ≤ p) ↔ (p ≥ 6) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (5 ≤ p) ↔ (p ≥ 6) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(0 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(6 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(0 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(1 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(5 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(4 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(6 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(7 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(1 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(5 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(6 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(7 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(5 : ℕ), (7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(4 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (p ≥ 6)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (p ≥ 6)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (p ≥ 6)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (p ≥ 6)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (p ≥ 6)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (p ≥ 6)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (p ≥ 6)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (p ≥ 6)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (p ≥ 6)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p k : ℕ) (hp : p.Prime) (hp5 : 4 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 4 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) →
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 4 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) →
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 4 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) →
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 4 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) →
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 4 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) →
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 4 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) →
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 4 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) →
    (∀ (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k), (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (5 ≤ p) ↔ (4 ≤ p) := by
  omega

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (5 ≤ p) ↔ (4 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (5 ≤ p) ↔ (4 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (5 ≤ p) ↔ (4 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (5 ≤ p) ↔ (4 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (5 ≤ p) ↔ (4 ≤ p) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (5 ≤ p) ↔ (4 ≤ p) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(0 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(6 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(1 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(5 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(4 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(6 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(5 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(6 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ), (p.Prime) ∧ (0 < k) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(4 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (4 ≤ p)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (4 ≤ p)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (4 ≤ p)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (4 ≤ p)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (4 ≤ p)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (4 ≤ p)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (4 ≤ p)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((5 ≤ p) ↔ (4 ≤ p)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
