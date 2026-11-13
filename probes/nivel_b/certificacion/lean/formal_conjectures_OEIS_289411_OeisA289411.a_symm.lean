import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Symmetry of digit sum differences $\operatorname{sign}(S_5(k) - S_1(k))$

a: $\mathrm{a}(n) = \sum_{k=0}^n \mathrm{sign}(\mathrm{A007953}(5k) - \mathrm{A007953}(k))$.
$\mathrm{A007953}(n)$ is the digital sum of $n$ in base 10.
The sequence is non-negative, so the sum over $\mathbb{Z}$ is converted to $\mathbb{N}$.

*References:*
- [A289411](https://oeis.org/A289411)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
- [A007953](https://oeis.org/A007953)
-/

section

namespace OeisA289411

open Nat

/--
a: $\mathrm{a}(n) = \sum_{k=0}^n \mathrm{sign}(\mathrm{A007953}(5k) - \mathrm{A007953}(k))$.
$\mathrm{A007953}(n)$ is the digital sum of $n$ in base 10.
The sequence is non-negative, so the sum over $\mathbb{Z}$ is converted to $\mathbb{N}$.
-/
def a (n : ℕ) : ℕ :=
  let digital_sum_ten (m : ℕ) : ℕ := (Nat.digits 10 m).sum
  (Finset.range (n + 1)).sum (fun k =>
    Int.sign ((digital_sum_ten (5 * k) : ℤ) - (digital_sum_ten k : ℤ)))
  |>.toNat

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (0 < k) ∧ (¬(let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (0 < k) ∧ (¬(let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (0 < k) ∧ (¬(let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (0 < k) ∧ (¬(let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (0 < k) ∧ (¬(let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (0 < k) ∧ (¬(let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (0 < k) ∧ (¬(let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (0 < k) ∧ (¬(let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔ (let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔ (let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔ (let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔ (let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔ (let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔ (let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔ (let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔ (let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔ (let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k > 0), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (k > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (k > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (k > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (k > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (k > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (k > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (k > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (k > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔
    (∀ (k : ℕ) (hk : k > 0), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔
    (∀ (k : ℕ) (hk : k > 0), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔
    (∀ (k : ℕ) (hk : k > 0), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔
    (∀ (k : ℕ) (hk : k > 0), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i₁ : ℕ, i₁ ≤ m_k → a (m_k - i₁) = a (m_k + i₁)

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔ (let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i₁ : ℕ, i₁ ≤ m_k → a (m_k - i₁) = a (m_k + i₁)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔ (let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i₁ : ℕ, i₁ ≤ m_k → a (m_k - i₁) = a (m_k + i₁)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔ (let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i₁ : ℕ, i₁ ≤ m_k → a (m_k - i₁) = a (m_k + i₁)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔ (let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i₁ : ℕ, i₁ ≤ m_k → a (m_k - i₁) = a (m_k + i₁)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔ (let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i₁ : ℕ, i₁ ≤ m_k → a (m_k - i₁) = a (m_k + i₁)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔ (let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i₁ : ℕ, i₁ ≤ m_k → a (m_k - i₁) = a (m_k + i₁)) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔ (let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i₁ : ℕ, i₁ ≤ m_k → a (m_k - i₁) = a (m_k + i₁)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔ (let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i₁ : ℕ, i₁ ≤ m_k → a (m_k - i₁) = a (m_k + i₁)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i₁ : ℕ, i₁ ≤ m_k → a (m_k - i₁) = a (m_k + i₁)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i₁ : ℕ, i₁ ≤ m_k → a (m_k - i₁) = a (m_k + i₁)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i₁ : ℕ, i₁ ≤ m_k → a (m_k - i₁) = a (m_k + i₁)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i₁ : ℕ, i₁ ≤ m_k → a (m_k - i₁) = a (m_k + i₁)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk₀ : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔
    (∀ (k : ℕ) (hk₀ : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔
    (∀ (k : ℕ) (hk₀ : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔
    (∀ (k : ℕ) (hk₀ : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔
    (∀ (k : ℕ) (hk₀ : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : ¬(k ≤ 0)), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (¬(k ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (¬(k ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (¬(k ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (¬(k ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (¬(k ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (¬(k ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (¬(k ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (¬(k ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔
    (∀ (k : ℕ) (hk : ¬(k ≤ 0)), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔
    (∀ (k : ℕ) (hk : ¬(k ≤ 0)), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔
    (∀ (k : ℕ) (hk : ¬(k ≤ 0)), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔
    (∀ (k : ℕ) (hk : ¬(k ≤ 0)), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (1 ≤ k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (1 ≤ k) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (1 ≤ k) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (1 ≤ k) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (1 ≤ k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (1 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (1 ≤ k) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (1 ≤ k) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔
    (∀ (k : ℕ) (hk : 1 ≤ k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔
    (∀ (k : ℕ) (hk : 1 ≤ k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔
    (∀ (k : ℕ) (hk : 1 ≤ k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔
    (∀ (k : ℕ) (hk : 1 ≤ k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k > 0), let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 0), let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 0), let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 0), let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 0), let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 0), let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 0), let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 0), let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : k > 0), let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : k > 0), let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : k > 0), let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : k > 0), let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : k > 0), let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : k > 0), let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : k > 0), let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (0 < k) ∧ (¬(let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (0 < k) ∧ (¬(let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (0 < k) ∧ (¬(let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (0 < k) ∧ (¬(let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (0 < k) ∧ (¬(let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (0 < k) ∧ (¬(let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (0 < k) ∧ (¬(let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (0 < k) ∧ (¬(let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔ (let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔ (let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔ (let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔ (let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔ (let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔ (let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔ (let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔ (let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔ (let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : 1 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : 1 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : 1 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : 1 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : 1 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : 1 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : 1 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (0 < k) ↔ (1 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (0 < k) ↔ (1 < k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (0 < k) ↔ (1 < k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (0 < k) ↔ (1 < k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (0 < k) ↔ (1 < k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (0 < k) ↔ (1 < k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (0 < k) ↔ (1 < k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((0 < k) ↔ (1 < k))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((0 < k) ↔ (1 < k))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((0 < k) ↔ (1 < k))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((0 < k) ↔ (1 < k))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((0 < k) ↔ (1 < k))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((0 < k) ↔ (1 < k))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (1 < k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (1 < k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (1 < k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (1 < k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (1 < k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (1 < k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : 1 ≤ k), let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : 1 ≤ k), let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : 1 ≤ k), let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : 1 ≤ k), let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : 1 ≤ k), let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : 1 ≤ k), let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) →
    (∀ (k : ℕ) (hk : 1 ≤ k), let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (0 < k) ∧ (¬(let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (0 < k) ∧ (¬(let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (0 < k) ∧ (¬(let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (0 < k) ∧ (¬(let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (0 < k) ∧ (¬(let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (0 < k) ∧ (¬(let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (0 < k) ∧ (¬(let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (0 < k) ∧ (¬(let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔ (let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔ (let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔ (let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔ (let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔ (let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔ (let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔ (let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔ (let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i)) ↔ (let m_k : ℕ := (11 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 0 < k) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 0 < k) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 0 < k) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 0 < k) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 0 < k) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
