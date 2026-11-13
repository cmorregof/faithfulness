import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Tu-Deng Conjecture

*References:*
* [Tu, Z., Deng, Y., *A conjecture about binary strings and its applications on constructing
  Boolean functions with optimal algebraic immunity*, Des. Codes Cryptogr. **60** (2011),
  1–14](https://doi.org/10.1007/s10623-010-9413-9)
* [IACR ePrint 2009/272](https://eprint.iacr.org/2009/272)
* [LLX26] [Liu, R., Luo, H., Xie, T., *A Complete Proof for Tu-Deng Conjecture*, arXiv:2608.05187v2
  (2026)](https://arxiv.org/abs/2608.05187v2)
* [Cu26] [Cusick, T. W., *Proof of the TuDeng Conjecture*, arXiv:2608.14821
  (2026)](https://arxiv.org/abs/2608.14821)
* [Lean26] [A Lean 4 proof of the count form of the conjecture](https://github.com/ifeelok92/tu-deng-conjecture-lean-formal-proof/blob/3c00561415deedcdc56b9e803042c1d0f15f5d5b/TuDengFormal/FirstExitNat.lean#L529-L535),
  commit `3c005614`, theorem `TuDeng.FirstExit.tu_deng_conjecture_full`

For an integer $k \ge 2$, identify the residues modulo $2^k - 1$ with the integers
$0, 1, \dots, 2^k - 2$, and let $w(a)$ denote the binary weight of $a$ (the number of ones in
its binary expansion). The Tu-Deng conjecture states that for every residue $t \ne 0$,

$$\#\{(a, b) : a + b \equiv t \pmod{2^k - 1},\ w(a) + w(b) \le k - 1\} \le 2^{k-1}.$$

Tu and Deng showed that this combinatorial statement implies that their constructions of
Boolean functions (a bent class and a balanced class) achieve optimal algebraic immunity,
which is the motivation for the conjecture. They verified the conjecture numerically for
$k \le 29$ (Remark 3.1 of the ePrint version).

The conjecture is no longer open: [LLX26] and, independently, [Cu26] give complete proofs.
[Lean26] is a Lean 4 development of the same bound, stated for the count of natural-number
representatives $x < 2^k - 1$ rather than for the set of residue pairs used below.
-/

section

namespace TuDengConjecture

/-- The binary weight of a natural number: the number of ones in its binary expansion. -/
def binaryWeight (n : ℕ) : ℕ := (Nat.digits 2 n).sum

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0) :
    (2 ≤ k) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0) :
    (2 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0) :
    (2 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0) :
    (2 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0) :
    (2 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0) :
    (2 ≤ k) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0) :
    (2 ≤ k) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 < k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : 2 < k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : 2 < k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : 2 < k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : 2 < k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : 2 < k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : 2 < k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : 2 < k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0) :
    (2 ≤ k) ↔ (2 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0) :
    (2 ≤ k) ↔ (2 < k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0) :
    (2 ≤ k) ↔ (2 < k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0) :
    (2 ≤ k) ↔ (2 < k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0) :
    (2 ≤ k) ↔ (2 < k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0) :
    (2 ≤ k) ↔ (2 < k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0) :
    (2 ≤ k) ↔ (2 < k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (2 < k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (2 < k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (2 < k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (2 < k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (2 < k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (2 < k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0) :
    (2 ≤ k) ↔ (3 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0) :
    (2 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0) :
    (2 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0) :
    (2 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0) :
    (2 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0) :
    (2 ≤ k) ↔ (3 ≤ k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0) :
    (2 ≤ k) ↔ (3 ≤ k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 2) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) :
    (2 ≤ k) ↔ (k ≥ 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) :
    (2 ≤ k) ↔ (k ≥ 2) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) :
    (2 ≤ k) ↔ (k ≥ 2) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) :
    (2 ≤ k) ↔ (k ≥ 2) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) :
    (2 ≤ k) ↔ (k ≥ 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) :
    (2 ≤ k) ↔ (k ≥ 2) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) :
    (2 ≤ k) ↔ (k ≥ 2) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) :
    (2 ≤ k) ↔ (k ≥ 2) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) ↔
    (∀ (k : ℕ) (hk : k ≥ 2) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) ↔
    (∀ (k : ℕ) (hk : k ≥ 2) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) ↔
    (∀ (k : ℕ) (hk : k ≥ 2) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) ↔
    (∀ (k : ℕ) (hk : k ≥ 2) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : ¬(t = 0)), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) :
    (t ≠ 0) ↔ (¬(t = 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) :
    (t ≠ 0) ↔ (¬(t = 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) :
    (t ≠ 0) ↔ (¬(t = 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) :
    (t ≠ 0) ↔ (¬(t = 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) :
    (t ≠ 0) ↔ (¬(t = 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) :
    (t ≠ 0) ↔ (¬(t = 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) :
    (t ≠ 0) ↔ (¬(t = 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) :
    (t ≠ 0) ↔ (¬(t = 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) ↔
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : ¬(t = 0)), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) ↔
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : ¬(t = 0)), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) ↔
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : ¬(t = 0)), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) ↔
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : ¬(t = 0)), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk₀ : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) ↔
    (∀ (k : ℕ) (hk₀ : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) ↔
    (∀ (k : ℕ) (hk₀ : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) ↔
    (∀ (k : ℕ) (hk₀ : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) ↔
    (∀ (k : ℕ) (hk₀ : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : ¬(k < 2)) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) :
    (2 ≤ k) ↔ (¬(k < 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) :
    (2 ≤ k) ↔ (¬(k < 2)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) :
    (2 ≤ k) ↔ (¬(k < 2)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) :
    (2 ≤ k) ↔ (¬(k < 2)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) :
    (2 ≤ k) ↔ (¬(k < 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) :
    (2 ≤ k) ↔ (¬(k < 2)) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) :
    (2 ≤ k) ↔ (¬(k < 2)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) :
    (2 ≤ k) ↔ (¬(k < 2)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) ↔
    (∀ (k : ℕ) (hk : ¬(k < 2)) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) ↔
    (∀ (k : ℕ) (hk : ¬(k < 2)) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) ↔
    (∀ (k : ℕ) (hk : ¬(k < 2)) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) ↔
    (∀ (k : ℕ) (hk : ¬(k < 2)) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 < k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) :
    (2 ≤ k) ↔ (1 < k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) :
    (2 ≤ k) ↔ (1 < k) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) :
    (2 ≤ k) ↔ (1 < k) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) :
    (2 ≤ k) ↔ (1 < k) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) :
    (2 ≤ k) ↔ (1 < k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) :
    (2 ≤ k) ↔ (1 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) :
    (2 ≤ k) ↔ (1 < k) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) :
    (2 ≤ k) ↔ (1 < k) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) ↔
    (∀ (k : ℕ) (hk : 1 < k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) ↔
    (∀ (k : ℕ) (hk : 1 < k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) ↔
    (∀ (k : ℕ) (hk : 1 < k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) ↔
    (∀ (k : ℕ) (hk : 1 < k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k > 2) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : k > 2) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : k > 2) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : k > 2) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : k > 2) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : k > 2) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : k > 2) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : k > 2) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0) :
    (2 ≤ k) ↔ (k > 2) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0) :
    (2 ≤ k) ↔ (k > 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0) :
    (2 ≤ k) ↔ (k > 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0) :
    (2 ≤ k) ↔ (k > 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0) :
    (2 ≤ k) ↔ (k > 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0) :
    (2 ≤ k) ↔ (k > 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0) :
    (2 ≤ k) ↔ (k > 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k > 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k > 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k > 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k > 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k > 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k > 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 3) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : k ≥ 3) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : k ≥ 3) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : k ≥ 3) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : k ≥ 3) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : k ≥ 3) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : k ≥ 3) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : k ≥ 3) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0) :
    (2 ≤ k) ↔ (k ≥ 3) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0) :
    (2 ≤ k) ↔ (k ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0) :
    (2 ≤ k) ↔ (k ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0) :
    (2 ≤ k) ↔ (k ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0) :
    (2 ≤ k) ↔ (k ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0) :
    (2 ≤ k) ↔ (k ≥ 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0) :
    (2 ≤ k) ↔ (k ≥ 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k ≥ 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k ≥ 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k ≥ 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k ≥ 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k ≥ 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k ≥ 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k ≥ 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0) :
    (2 ≤ k) ↔ (1 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0) :
    (2 ≤ k) ↔ (1 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0) :
    (2 ≤ k) ↔ (1 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0) :
    (2 ≤ k) ↔ (1 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0) :
    (2 ≤ k) ↔ (1 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0) :
    (2 ≤ k) ↔ (1 ≤ k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0) :
    (2 ≤ k) ↔ (1 ≤ k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (1 ≤ k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (1 ≤ k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (1 ≤ k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (1 ≤ k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (1 ≤ k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (1 ≤ k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 < k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (3 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 < k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (3 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 < k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (3 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 < k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (3 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 < k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (3 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 < k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (3 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 < k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (3 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 < k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (3 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : 1 < k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (3 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : 1 < k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (3 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : 1 < k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (3 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : 1 < k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (3 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : 1 < k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (3 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : 1 < k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (3 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (2 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) →
    (∀ (k : ℕ) (hk : 1 < k) (t : ZMod (2 ^ k - 1)) (ht : t ≠ 0), {p : ZMod (3 ^ k - 1) × ZMod (2 ^ k - 1) |
        p.1 + p.2 = t ∧ binaryWeight p.1.val + binaryWeight p.2.val ≤ k - 1}.ncard
      ≤ 2 ^ (k - 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (hk : 2 ≤ k) (ht : t ≠ 0) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (hk : 2 ≤ k) (ht : t ≠ 0) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (hk : 2 ≤ k) (ht : t ≠ 0) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (hk : 2 ≤ k) (ht : t ≠ 0) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (t : ZMod (2 ^ k - 1)) (hk : 2 ≤ k) (ht : t ≠ 0) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
