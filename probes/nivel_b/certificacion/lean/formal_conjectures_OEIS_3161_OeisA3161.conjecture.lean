import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# A binomial coefficient sum

A binomial coefficient sum:
$$a(n) = \sum_{k=0}^{\lfloor n/2 \rfloor} \left( \binom{n}{k} - \binom{n}{k-1} \right)^3$$
where $\binom{n}{-1} = 0$.

*References:*
- [A003161](https://oeis.org/A003161)
- [Li26] Wentao Li, [A supercongruence for A003161](https://github.com/VictorLiwentao/lean-oeis-proofs/blob/41f7b2ba762827a74f1651e76a2ad6d77be6a021/proofs/new-formalization/A003161/PROOF.md), 2026.
-/

section

namespace OeisA3161

/-- A binomial coefficient sum:
$a(n) = \sum_{k=0}^{\lfloor n/2 \rfloor} (\binom{n}{k} - \binom{n}{k-1})^3$. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n / 2 + 1),
    let diff : ℤ := (n.choose k : ℤ) - (if k = 0 then 0 else (n.choose (k - 1) : ℤ))
    (diff ^ 3).toNat

/-- Auxiliary sequence $b(n) = a(2n-1)$. -/
def b (n : ℕ) : ℕ :=
  a (2 * n - 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k p : ℕ) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p) :
    (0 < n) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p) :
    (0 < n) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p) :
    (0 < n) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(5 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(5 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(5 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(4 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (6 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(5 : ℕ), (0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(5 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(5 : ℕ), (5 : ℕ), (0 : ℕ), by norm_num⟩

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
  ∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 < p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 < p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 < p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 < p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 < p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 < p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 < p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 < p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) :
    (5 ≤ p) ↔ (5 < p) := by
  omega

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) :
    (5 ≤ p) ↔ (5 < p) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) :
    (5 ≤ p) ↔ (5 < p) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) :
    (5 ≤ p) ↔ (5 < p) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) :
    (5 ≤ p) ↔ (5 < p) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) :
    (5 ≤ p) ↔ (5 < p) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) :
    (5 ≤ p) ↔ (5 < p) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(5 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(1 : ℕ), (0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(1 : ℕ), (5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(5 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(5 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(4 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (0 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (6 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(1 : ℕ), (0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(1 : ℕ), (1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(1 : ℕ), (5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(1 : ℕ), (4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(5 : ℕ), (0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(5 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(5 : ℕ), (5 : ℕ), (0 : ℕ), by norm_num⟩

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
  ∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 6 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 6 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 6 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 6 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 6 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 6 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 6 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 6 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) :
    (5 ≤ p) ↔ (6 ≤ p) := by
  omega

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) :
    (5 ≤ p) ↔ (6 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) :
    (5 ≤ p) ↔ (6 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) :
    (5 ≤ p) ↔ (6 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) :
    (5 ≤ p) ↔ (6 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) :
    (5 ≤ p) ↔ (6 ≤ p) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) :
    (5 ≤ p) ↔ (6 ≤ p) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(5 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(5 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(5 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(4 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (0 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (6 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(5 : ℕ), (0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(5 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(5 : ℕ), (5 : ℕ), (0 : ℕ), by norm_num⟩

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
  ∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k p : ℕ) (hn : n > 0) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]

set_option maxHeartbeats 200000 in
example (n k p : ℕ) :
    (0 < n) ↔ (n > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n k p : ℕ) :
    (0 < n) ↔ (n > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n k p : ℕ) :
    (0 < n) ↔ (n > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n k p : ℕ) :
    (0 < n) ↔ (n > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n k p : ℕ) :
    (0 < n) ↔ (n > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n k p : ℕ) :
    (0 < n) ↔ (n > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (n k p : ℕ) :
    (0 < n) ↔ (n > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n k p : ℕ) :
    (0 < n) ↔ (n > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) ↔
    (∀ (n k p : ℕ) (hn : n > 0) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) ↔
    (∀ (n k p : ℕ) (hn : n > 0) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) ↔
    (∀ (n k p : ℕ) (hn : n > 0) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) ↔
    (∀ (n k p : ℕ) (hn : n > 0) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k p : ℕ) (hk : 0 < k) (hn : 0 < n) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) ↔
    (∀ (n k p : ℕ) (hk : 0 < k) (hn : 0 < n) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) ↔
    (∀ (n k p : ℕ) (hk : 0 < k) (hn : 0 < n) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) ↔
    (∀ (n k p : ℕ) (hk : 0 < k) (hn : 0 < n) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) ↔
    (∀ (n k p : ℕ) (hk : 0 < k) (hn : 0 < n) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k p : ℕ) (hn₀ : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) ↔
    (∀ (n k p : ℕ) (hn₀ : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) ↔
    (∀ (n k p : ℕ) (hn₀ : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) ↔
    (∀ (n k p : ℕ) (hn₀ : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) ↔
    (∀ (n k p : ℕ) (hn₀ : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k p : ℕ) (hn : ¬(n ≤ 0)) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]

set_option maxHeartbeats 200000 in
example (n k p : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n k p : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n k p : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n k p : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n k p : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n k p : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (n k p : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n k p : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) ↔
    (∀ (n k p : ℕ) (hn : ¬(n ≤ 0)) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) ↔
    (∀ (n k p : ℕ) (hn : ¬(n ≤ 0)) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) ↔
    (∀ (n k p : ℕ) (hn : ¬(n ≤ 0)) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) ↔
    (∀ (n k p : ℕ) (hn : ¬(n ≤ 0)) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k p : ℕ) (hn : 1 ≤ n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]

set_option maxHeartbeats 200000 in
example (n k p : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n k p : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n k p : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n k p : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n k p : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n k p : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n k p : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n k p : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) ↔
    (∀ (n k p : ℕ) (hn : 1 ≤ n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) ↔
    (∀ (n k p : ℕ) (hn : 1 ≤ n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) ↔
    (∀ (n k p : ℕ) (hn : 1 ≤ n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) ↔
    (∀ (n k p : ℕ) (hn : 1 ≤ n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k p : ℕ) (hn : n > 0) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 < p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : n > 0) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 < p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : n > 0) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 < p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : n > 0) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 < p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : n > 0) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 < p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : n > 0) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 < p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : n > 0) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 < p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : n > 0) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 < p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) :
    (5 ≤ p) ↔ (5 < p) := by
  omega

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) :
    (5 ≤ p) ↔ (5 < p) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) :
    (5 ≤ p) ↔ (5 < p) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) :
    (5 ≤ p) ↔ (5 < p) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) :
    (5 ≤ p) ↔ (5 < p) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) :
    (5 ≤ p) ↔ (5 < p) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) :
    (5 ≤ p) ↔ (5 < p) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(5 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(1 : ℕ), (0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(1 : ℕ), (5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(5 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(5 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(4 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (0 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (6 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(1 : ℕ), (0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(1 : ℕ), (1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(1 : ℕ), (5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(1 : ℕ), (4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(5 : ℕ), (0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(5 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(5 : ℕ), (5 : ℕ), (0 : ℕ), by norm_num⟩

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
  ∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k p : ℕ) (hn : n > 0) (hk : 0 < k) (hp : p.Prime) (hp_ge : 6 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : n > 0) (hk : 0 < k) (hp : p.Prime) (hp_ge : 6 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : n > 0) (hk : 0 < k) (hp : p.Prime) (hp_ge : 6 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : n > 0) (hk : 0 < k) (hp : p.Prime) (hp_ge : 6 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : n > 0) (hk : 0 < k) (hp : p.Prime) (hp_ge : 6 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : n > 0) (hk : 0 < k) (hp : p.Prime) (hp_ge : 6 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : n > 0) (hk : 0 < k) (hp : p.Prime) (hp_ge : 6 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : n > 0) (hk : 0 < k) (hp : p.Prime) (hp_ge : 6 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) :
    (5 ≤ p) ↔ (6 ≤ p) := by
  omega

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) :
    (5 ≤ p) ↔ (6 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) :
    (5 ≤ p) ↔ (6 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) :
    (5 ≤ p) ↔ (6 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) :
    (5 ≤ p) ↔ (6 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) :
    (5 ≤ p) ↔ (6 ≤ p) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) :
    (5 ≤ p) ↔ (6 ≤ p) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(5 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(5 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(5 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(4 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (0 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (6 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(5 : ℕ), (0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(5 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(5 : ℕ), (5 : ℕ), (0 : ℕ), by norm_num⟩

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
  ∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k p : ℕ) (hn : 1 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : 1 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : 1 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : 1 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : 1 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : 1 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : 1 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : 1 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p) :
    (0 < n) ↔ (1 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p) :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p) :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p) :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p) :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p) :
    (0 < n) ↔ (1 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p) :
    (0 < n) ↔ (1 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(5 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), (0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), (5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(5 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(5 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(4 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (0 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (6 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), (0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), (1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), (5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), (4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(5 : ℕ), (0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(5 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < k) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(5 : ℕ), (5 : ℕ), (0 : ℕ), by norm_num⟩

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
  ∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k p : ℕ) (hn : 1 ≤ n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 6 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : 1 ≤ n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 6 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : 1 ≤ n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 6 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : 1 ≤ n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 6 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : 1 ≤ n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 6 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : 1 ≤ n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 6 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : 1 ≤ n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 6 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : 1 ≤ n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 6 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) :
    (5 ≤ p) ↔ (6 ≤ p) := by
  omega

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) :
    (5 ≤ p) ↔ (6 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) :
    (5 ≤ p) ↔ (6 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) :
    (5 ≤ p) ↔ (6 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) :
    (5 ≤ p) ↔ (6 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) :
    (5 ≤ p) ↔ (6 ≤ p) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) :
    (5 ≤ p) ↔ (6 ≤ p) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(5 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(5 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(5 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(4 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (0 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (6 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(5 : ℕ), (0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(5 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (0 < k) ∧ (p.Prime) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(5 : ℕ), (5 : ℕ), (0 : ℕ), by norm_num⟩

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
  ∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k p : ℕ) (hn : 0 < n) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k p : ℕ) (hn : 0 < n) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) →
    (∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p), (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hn : 0 < n) (hp : p.Prime) (hp_ge : 5 ≤ p) :
    (0 < k) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hn : 0 < n) (hp : p.Prime) (hp_ge : 5 ≤ p) :
    (0 < k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hn : 0 < n) (hp : p.Prime) (hp_ge : 5 ≤ p) :
    (0 < k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hn : 0 < n) (hp : p.Prime) (hp_ge : 5 ≤ p) :
    (0 < k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hn : 0 < n) (hp : p.Prime) (hp_ge : 5 ≤ p) :
    (0 < k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hn : 0 < n) (hp : p.Prime) (hp_ge : 5 ≤ p) :
    (0 < k) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hn : 0 < n) (hp : p.Prime) (hp_ge : 5 ≤ p) :
    (0 < k) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(5 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(0 : ℕ), (4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(5 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(5 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(4 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(0 : ℕ), (4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(0 : ℕ), (6 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(1 : ℕ), (4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(5 : ℕ), (0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(5 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (p : ℕ), (0 < n) ∧ (p.Prime) ∧ (5 ≤ p) ∧ (¬((0 < k) ↔ (True))) :=
  ⟨(5 : ℕ), (5 : ℕ), (0 : ℕ), by norm_num⟩

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
example (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
