import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Number of Abelian cubes of length $3n$ over an alphabet of size 3

An Abelian cube is a string of the form $x x' x''$ with $|x| = |x'| = |x''|$ and $x$ is a
permutation of $x'$ and $x''$. The number of Abelian cubes of length $3n$ over an alphabet of
size 3 is given by
$$a(n) = \sum_{k=0}^n \binom{n}{k}^3 \sum_{j=0}^k \binom{k}{j}^3.$$

*References:*
- [A141057](https://oeis.org/A141057)-/

section

namespace OeisA141057

/-- Number of Abelian cubes of length $3n$ over an alphabet of size 3. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), (n.choose k ^ 3) * ∑ j ∈ Finset.range (k + 1), (k.choose j ^ 3)

/-- Extension of the sequence $a$ to all integers $n \in \mathbb{Z}$.
For $n < 0$, $a(n) = \sum_{k=0}^{-n} \binom{n}{k}^3 \sum_{j=0}^k \binom{k}{j}^3$,
where $\binom{n}{k} = (-1)^k \binom{-n+k-1}{k}$. -/
def aInt (n : ℤ) : ℤ :=
  if 0 ≤ n then
    let nNat := n.toNat
    (∑ k ∈ Finset.range (nNat + 1), (nNat.choose k ^ 3) * ∑ j ∈ Finset.range (k + 1), (k.choose j ^ 3) : ℕ)
  else
    let nNat := (-n).toNat
    ∑ k ∈ Finset.range (nNat + 1), ((-1 : ℤ) ^ k * (nNat + k - 1).choose k : ℤ) ^ 3 *
      ∑ j ∈ Finset.range (k + 1), ((k.choose j : ℤ) ^ 3)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    (5 ≤ p) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    (5 ≤ p) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    (5 ≤ p) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    (5 ≤ p) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    (5 ≤ p) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    (5 ≤ p) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    (5 ≤ p) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(5 : ℕ), (1 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(1 : ℕ), (4 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), (1 : ℤ), by norm_num⟩

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
  ∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 < p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 < p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 < p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 < p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 < p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 < p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 < p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 < p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    (5 ≤ p) ↔ (5 < p) := by
  omega

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    (5 ≤ p) ↔ (5 < p) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    (5 ≤ p) ↔ (5 < p) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    (5 ≤ p) ↔ (5 < p) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    (5 ≤ p) ↔ (5 < p) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    (5 ≤ p) ↔ (5 < p) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    (5 ≤ p) ↔ (5 < p) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(1 : ℕ), (1 : ℕ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(1 : ℕ), (5 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(5 : ℕ), (1 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(1 : ℕ), (1 : ℕ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(1 : ℕ), (0 : ℕ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(1 : ℕ), (2 : ℕ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(1 : ℕ), (5 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(1 : ℕ), (4 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (1 : ℕ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(0 : ℕ), (5 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(2 : ℕ), (1 : ℕ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (5 < p))) :=
  ⟨(2 : ℕ), (2 : ℕ), (1 : ℤ), by norm_num⟩

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
  ∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 6 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 6 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 6 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 6 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 6 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 6 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 6 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 6 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    (5 ≤ p) ↔ (6 ≤ p) := by
  omega

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    (5 ≤ p) ↔ (6 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    (5 ≤ p) ↔ (6 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    (5 ≤ p) ↔ (6 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    (5 ≤ p) ↔ (6 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    (5 ≤ p) ↔ (6 ≤ p) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    (5 ≤ p) ↔ (6 ≤ p) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (1 : ℕ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (5 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(5 : ℕ), (1 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (1 : ℕ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (0 : ℕ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (2 : ℕ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (5 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(1 : ℕ), (4 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (1 : ℕ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(0 : ℕ), (5 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(2 : ℕ), (1 : ℕ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (6 ≤ p))) :=
  ⟨(2 : ℕ), (2 : ℕ), (1 : ℤ), by norm_num⟩

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
  ∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : p ≥ 5) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) :
    (5 ≤ p) ↔ (p ≥ 5) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) :
    (5 ≤ p) ↔ (p ≥ 5) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) :
    (5 ≤ p) ↔ (p ≥ 5) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) :
    (5 ≤ p) ↔ (p ≥ 5) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) :
    (5 ≤ p) ↔ (p ≥ 5) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) :
    (5 ≤ p) ↔ (p ≥ 5) := by
  omega

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) :
    (5 ≤ p) ↔ (p ≥ 5) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) :
    (5 ≤ p) ↔ (p ≥ 5) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : p ≥ 5) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : p ≥ 5) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : p ≥ 5) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : p ≥ 5) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : ¬(n = 0)), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) :
    (n ≠ 0) ↔ (¬(n = 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) :
    (n ≠ 0) ↔ (¬(n = 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) :
    (n ≠ 0) ↔ (¬(n = 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) :
    (n ≠ 0) ↔ (¬(n = 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) :
    (n ≠ 0) ↔ (¬(n = 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) :
    (n ≠ 0) ↔ (¬(n = 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) :
    (n ≠ 0) ↔ (¬(n = 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) :
    (n ≠ 0) ↔ (¬(n = 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : ¬(n = 0)), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : ¬(n = 0)), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : ¬(n = 0)), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : ¬(n = 0)), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p k : ℕ) (n : ℤ) (h_p_ge_5 : 5 ≤ p) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔
    (∀ (p k : ℕ) (n : ℤ) (h_p_ge_5 : 5 ≤ p) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔
    (∀ (p k : ℕ) (n : ℤ) (h_p_ge_5 : 5 ≤ p) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔
    (∀ (p k : ℕ) (n : ℤ) (h_p_ge_5 : 5 ≤ p) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔
    (∀ (p k : ℕ) (n : ℤ) (h_p_ge_5 : 5 ≤ p) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p k : ℕ) (n : ℤ) (hp₀ : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔
    (∀ (p k : ℕ) (n : ℤ) (hp₀ : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔
    (∀ (p k : ℕ) (n : ℤ) (hp₀ : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔
    (∀ (p k : ℕ) (n : ℤ) (hp₀ : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔
    (∀ (p k : ℕ) (n : ℤ) (hp₀ : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : ¬(p < 5)) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) :
    (5 ≤ p) ↔ (¬(p < 5)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) :
    (5 ≤ p) ↔ (¬(p < 5)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) :
    (5 ≤ p) ↔ (¬(p < 5)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) :
    (5 ≤ p) ↔ (¬(p < 5)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) :
    (5 ≤ p) ↔ (¬(p < 5)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) :
    (5 ≤ p) ↔ (¬(p < 5)) := by
  omega

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) :
    (5 ≤ p) ↔ (¬(p < 5)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) :
    (5 ≤ p) ↔ (¬(p < 5)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : ¬(p < 5)) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : ¬(p < 5)) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : ¬(p < 5)) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : ¬(p < 5)) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 4 < p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) :
    (5 ≤ p) ↔ (4 < p) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) :
    (5 ≤ p) ↔ (4 < p) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) :
    (5 ≤ p) ↔ (4 < p) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) :
    (5 ≤ p) ↔ (4 < p) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) :
    (5 ≤ p) ↔ (4 < p) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) :
    (5 ≤ p) ↔ (4 < p) := by
  omega

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) :
    (5 ≤ p) ↔ (4 < p) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) :
    (5 ≤ p) ↔ (4 < p) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 4 < p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 4 < p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 4 < p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 4 < p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : p > 5) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : p > 5) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : p > 5) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : p > 5) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : p > 5) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : p > 5) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : p > 5) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : p > 5) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    (5 ≤ p) ↔ (p > 5) := by
  omega

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    (5 ≤ p) ↔ (p > 5) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    (5 ≤ p) ↔ (p > 5) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    (5 ≤ p) ↔ (p > 5) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    (5 ≤ p) ↔ (p > 5) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    (5 ≤ p) ↔ (p > 5) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    (5 ≤ p) ↔ (p > 5) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(1 : ℕ), (1 : ℕ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(1 : ℕ), (5 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(5 : ℕ), (1 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(1 : ℕ), (1 : ℕ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(1 : ℕ), (0 : ℕ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(1 : ℕ), (2 : ℕ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(1 : ℕ), (5 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(1 : ℕ), (4 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(0 : ℕ), (1 : ℕ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(0 : ℕ), (5 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(2 : ℕ), (1 : ℕ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p > 5))) :=
  ⟨(2 : ℕ), (2 : ℕ), (1 : ℤ), by norm_num⟩

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
  ∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : p ≥ 6) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : p ≥ 6) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : p ≥ 6) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : p ≥ 6) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : p ≥ 6) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : p ≥ 6) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : p ≥ 6) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : p ≥ 6) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    (5 ≤ p) ↔ (p ≥ 6) := by
  omega

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    (5 ≤ p) ↔ (p ≥ 6) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    (5 ≤ p) ↔ (p ≥ 6) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    (5 ≤ p) ↔ (p ≥ 6) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    (5 ≤ p) ↔ (p ≥ 6) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    (5 ≤ p) ↔ (p ≥ 6) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    (5 ≤ p) ↔ (p ≥ 6) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(1 : ℕ), (1 : ℕ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(1 : ℕ), (5 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(5 : ℕ), (1 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(1 : ℕ), (1 : ℕ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(1 : ℕ), (0 : ℕ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(1 : ℕ), (2 : ℕ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(1 : ℕ), (5 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(1 : ℕ), (4 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(0 : ℕ), (1 : ℕ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(0 : ℕ), (5 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(2 : ℕ), (1 : ℕ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (p ≥ 6))) :=
  ⟨(2 : ℕ), (2 : ℕ), (1 : ℤ), by norm_num⟩

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
  ∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 4 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 4 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 4 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 4 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 4 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 4 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 4 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 4 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    (5 ≤ p) ↔ (4 ≤ p) := by
  omega

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    (5 ≤ p) ↔ (4 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    (5 ≤ p) ↔ (4 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    (5 ≤ p) ↔ (4 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    (5 ≤ p) ↔ (4 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    (5 ≤ p) ↔ (4 ≤ p) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    (5 ≤ p) ↔ (4 ≤ p) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(1 : ℕ), (1 : ℕ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(1 : ℕ), (5 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(5 : ℕ), (1 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(1 : ℕ), (1 : ℕ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(1 : ℕ), (0 : ℕ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(1 : ℕ), (2 : ℕ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(1 : ℕ), (5 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(1 : ℕ), (4 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(0 : ℕ), (1 : ℕ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(0 : ℕ), (5 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(2 : ℕ), (1 : ℕ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬((5 ≤ p) ↔ (4 ≤ p))) :=
  ⟨(2 : ℕ), (2 : ℕ), (1 : ℤ), by norm_num⟩

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
example : Prop :=
  ∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 4 < p) (h_k_pos : 1 < k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 4 < p) (h_k_pos : 1 < k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 4 < p) (h_k_pos : 1 < k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 4 < p) (h_k_pos : 1 < k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 4 < p) (h_k_pos : 1 < k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 4 < p) (h_k_pos : 1 < k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 4 < p) (h_k_pos : 1 < k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 4 < p) (h_k_pos : 1 < k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (hn : n ≠ 0) :
    (1 ≤ k) ↔ (1 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (hn : n ≠ 0) :
    (1 ≤ k) ↔ (1 < k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (hn : n ≠ 0) :
    (1 ≤ k) ↔ (1 < k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (hn : n ≠ 0) :
    (1 ≤ k) ↔ (1 < k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (hn : n ≠ 0) :
    (1 ≤ k) ↔ (1 < k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (hn : n ≠ 0) :
    (1 ≤ k) ↔ (1 < k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (hn : n ≠ 0) :
    (1 ≤ k) ↔ (1 < k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (n ≠ 0) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(5 : ℕ), (5 : ℕ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (n ≠ 0) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(5 : ℕ), (5 : ℕ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (n ≠ 0) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(5 : ℕ), (4 : ℕ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (n ≠ 0) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(4 : ℕ), (5 : ℕ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (n ≠ 0) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(5 : ℕ), (5 : ℕ), (6 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (n ≠ 0) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(5 : ℕ), (4 : ℕ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (n ≠ 0) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(5 : ℕ), (6 : ℕ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (n ≠ 0) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(4 : ℕ), (5 : ℕ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (n ≠ 0) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(4 : ℕ), (4 : ℕ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (n ≠ 0) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(6 : ℕ), (5 : ℕ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (n ≠ 0) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(5 : ℕ), (5 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (n ≠ 0) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(5 : ℕ), (4 : ℕ), (6 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (n ≠ 0) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(5 : ℕ), (6 : ℕ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (n ≠ 0) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(5 : ℕ), (0 : ℕ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (n ≠ 0) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(4 : ℕ), (5 : ℕ), (6 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (n ≠ 0) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(4 : ℕ), (4 : ℕ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (n ≠ 0) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(4 : ℕ), (6 : ℕ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (n ≠ 0) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(6 : ℕ), (5 : ℕ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (n ≠ 0) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(6 : ℕ), (4 : ℕ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (n ≠ 0) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(0 : ℕ), (5 : ℕ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (n ≠ 0) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(5 : ℕ), (5 : ℕ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (n ≠ 0) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(5 : ℕ), (4 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (n ≠ 0) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(5 : ℕ), (6 : ℕ), (6 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (n ≠ 0) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(5 : ℕ), (0 : ℕ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (n ≠ 0) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(5 : ℕ), (1 : ℕ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (n ≠ 0) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(4 : ℕ), (5 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (n ≠ 0) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(4 : ℕ), (4 : ℕ), (6 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (n ≠ 0) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(4 : ℕ), (6 : ℕ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (n ≠ 0) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(4 : ℕ), (0 : ℕ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (n ≠ 0) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(6 : ℕ), (5 : ℕ), (6 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (n ≠ 0) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(6 : ℕ), (4 : ℕ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (n ≠ 0) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(6 : ℕ), (6 : ℕ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (1 < k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (1 < k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (1 < k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (1 < k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (1 < k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (1 < k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 4 < p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)]

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 4 < p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 4 < p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 4 < p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 4 < p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 4 < p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 4 < p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 4 < p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 4 < p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)]) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 4 < p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)]) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 4 < p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)]) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 4 < p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)]) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 4 < p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)]) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 4 < p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)]) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) →
    (∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 4 < p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0), aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)]) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬(aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(5 : ℕ), (5 : ℕ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬(aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(5 : ℕ), (5 : ℕ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬(aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(5 : ℕ), (4 : ℕ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬(aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(4 : ℕ), (5 : ℕ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬(aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(5 : ℕ), (5 : ℕ), (6 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬(aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(5 : ℕ), (4 : ℕ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬(aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(5 : ℕ), (6 : ℕ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬(aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(4 : ℕ), (5 : ℕ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬(aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(4 : ℕ), (4 : ℕ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬(aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(6 : ℕ), (5 : ℕ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬(aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(5 : ℕ), (5 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬(aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(5 : ℕ), (4 : ℕ), (6 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬(aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(5 : ℕ), (6 : ℕ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬(aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(5 : ℕ), (1 : ℕ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬(aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(4 : ℕ), (5 : ℕ), (6 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬(aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(4 : ℕ), (4 : ℕ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬(aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(4 : ℕ), (6 : ℕ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬(aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(6 : ℕ), (5 : ℕ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬(aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(6 : ℕ), (4 : ℕ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬(aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(1 : ℕ), (5 : ℕ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬(aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(5 : ℕ), (5 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬(aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(5 : ℕ), (4 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬(aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(5 : ℕ), (6 : ℕ), (6 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬(aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(5 : ℕ), (1 : ℕ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬(aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(5 : ℕ), (0 : ℕ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬(aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(4 : ℕ), (5 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬(aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(4 : ℕ), (4 : ℕ), (6 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬(aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(4 : ℕ), (6 : ℕ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬(aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(4 : ℕ), (1 : ℕ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬(aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(6 : ℕ), (5 : ℕ), (6 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬(aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(6 : ℕ), (4 : ℕ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), (p.Prime) ∧ (5 ≤ p) ∧ (1 ≤ k) ∧ (n ≠ 0) ∧ (¬(aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(6 : ℕ), (6 : ℕ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), ¬((aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔ (aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), ¬((aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔ (aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), ¬((aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔ (aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), ¬((aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔ (aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), ¬((aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔ (aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), ¬((aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔ (aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), ¬((aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔ (aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), ¬((aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔ (aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), ¬((aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔ (aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), ¬((aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔ (aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), ¬((aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔ (aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(1 : ℕ), (1 : ℕ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), ¬((aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔ (aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), ¬((aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔ (aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), ¬((aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔ (aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(1 : ℕ), (3 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), ¬((aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔ (aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), ¬((aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔ (aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), ¬((aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔ (aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), ¬((aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔ (aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), ¬((aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔ (aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), ¬((aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔ (aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(3 : ℕ), (1 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), ¬((aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔ (aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(1 : ℕ), (1 : ℕ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), ¬((aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔ (aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(1 : ℕ), (0 : ℕ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), ¬((aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔ (aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(1 : ℕ), (2 : ℕ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), ¬((aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔ (aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(1 : ℕ), (3 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), ¬((aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔ (aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(1 : ℕ), (4 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), ¬((aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔ (aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(0 : ℕ), (1 : ℕ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), ¬((aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔ (aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), ¬((aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔ (aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), ¬((aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔ (aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(0 : ℕ), (3 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), ¬((aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔ (aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(2 : ℕ), (1 : ℕ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), ¬((aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔ (aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ) (k : ℕ) (n : ℤ), ¬((aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]) ↔ (aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (4 * k) : ℤ)])) :=
  ⟨(2 : ℕ), (2 : ℕ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k) (hn : n ≠ 0) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
