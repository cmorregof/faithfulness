import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Primality and primitive root property from divisibility $n \mid (a(n-1) + 2^{n-2})$

$a(n) = \frac{2^{n-1}}{n!} \prod_{k=1}^{n-1} (2^k-1)$.
The sequence $a(n)$ is composed of natural numbers, thus we define it
as a function $\mathbb{N} \to \mathbb{N}$.

*References:*
- [A091669](https://oeis.org/A091669)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/

section

namespace OeisA91669

open Nat BigOperators

/--
$a(n) = \frac{2^{n-1}}{n!} \prod_{k=1}^{n-1} (2^k-1)$.
The sequence $a(n)$ is composed of natural numbers, thus we define it
as a function $\mathbb{N} \to \mathbb{N}$.
-/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0 -- Sequence is defined for n >= 1.
  else
    let n_pred : ℕ := n.pred

    -- The numerator of the expression. Both factors are in ℕ.
    let numerator : ℕ := (2 ^ n_pred) * (Finset.Ico 1 n).prod (fun k => 2 ^ k - 1)

    -- The denominator is $n!$.
    let denominator : ℕ := n.factorial

    -- The division is exact, since the result is an integer sequence.
    numerator / denominator

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) →
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) →
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) →
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) →
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) →
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) →
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) →
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 2) ↔ (n ≥ 2) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 2) ↔ (n ≥ 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 2) ↔ (n ≥ 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 2) ↔ (n ≥ 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 2) ↔ (n ≥ 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 2) ↔ (n ≥ 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 2) ↔ (n ≥ 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 2) ↔ (n ≥ 2))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 2) ↔ (n ≥ 2))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 2) ↔ (n ≥ 2))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 2) ↔ (n ≥ 2))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 2) ↔ (n ≥ 2))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 2) ↔ (n ≥ 2))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 2) ↔ (n ≥ 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 2) ↔ (n ≥ 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 2) ↔ (n ≥ 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 2) ↔ (n ≥ 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 2) ↔ (n ≥ 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 2) ↔ (n ≥ 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 3), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) →
    (∀ (n : ℕ) (hn : n > 3), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) →
    (∀ (n : ℕ) (hn : n > 3), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) →
    (∀ (n : ℕ) (hn : n > 3), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) →
    (∀ (n : ℕ) (hn : n > 3), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) →
    (∀ (n : ℕ) (hn : n > 3), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) →
    (∀ (n : ℕ) (hn : n > 3), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) →
    (∀ (n : ℕ) (hn : n > 3), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 2) ↔ (n > 3) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 2) ↔ (n > 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 2) ↔ (n > 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 2) ↔ (n > 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 2) ↔ (n > 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 2) ↔ (n > 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 2) ↔ (n > 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 2) ↔ (n > 3))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 2) ↔ (n > 3))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 2) ↔ (n > 3))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 2) ↔ (n > 3))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 2) ↔ (n > 3))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 2) ↔ (n > 3))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 2) ↔ (n > 3))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 2) ↔ (n > 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 2) ↔ (n > 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 2) ↔ (n > 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 2) ↔ (n > 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 2) ↔ (n > 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 2) ↔ (n > 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 2) ↔ (n > 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 < n), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 2) ↔ (2 < n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 2) ↔ (2 < n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 2) ↔ (2 < n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 2) ↔ (2 < n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 2) ↔ (2 < n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 2) ↔ (2 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 2) ↔ (2 < n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 2) ↔ (2 < n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) ↔
    (∀ (n : ℕ) (hn : 2 < n), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) ↔
    (∀ (n : ℕ) (hn : 2 < n), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) ↔
    (∀ (n : ℕ) (hn : 2 < n), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) ↔
    (∀ (n : ℕ) (hn : 2 < n), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn₀ : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) ↔
    (∀ (n : ℕ) (hn₀ : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) ↔
    (∀ (n : ℕ) (hn₀ : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) ↔
    (∀ (n : ℕ) (hn₀ : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) ↔
    (∀ (n : ℕ) (hn₀ : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : ¬(n ≤ 2)), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 2) ↔ (¬(n ≤ 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 2) ↔ (¬(n ≤ 2)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 2) ↔ (¬(n ≤ 2)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 2) ↔ (¬(n ≤ 2)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 2) ↔ (¬(n ≤ 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 2) ↔ (¬(n ≤ 2)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 2) ↔ (¬(n ≤ 2)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 2) ↔ (¬(n ≤ 2)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 2)), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 2)), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 2)), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 2)), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 3), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 2) ↔ (n ≥ 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 2) ↔ (n ≥ 3) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 2) ↔ (n ≥ 3) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 2) ↔ (n ≥ 3) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 2) ↔ (n ≥ 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 2) ↔ (n ≥ 3) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 2) ↔ (n ≥ 3) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n > 2) ↔ (n ≥ 3) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) ↔
    (∀ (n : ℕ) (hn : n ≥ 3), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) ↔
    (∀ (n : ℕ) (hn : n ≥ 3), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) ↔
    (∀ (n : ℕ) (hn : n ≥ 3), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) ↔
    (∀ (n : ℕ) (hn : n ≥ 3), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) →
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) →
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) →
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) →
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) →
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) →
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) →
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 2) ↔ (2 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 2) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 2) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 2) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 2) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 2) ↔ (2 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 2) ↔ (2 ≤ n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 2) ↔ (2 ≤ n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 2) ↔ (2 ≤ n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 2) ↔ (2 ≤ n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 2) ↔ (2 ≤ n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 2) ↔ (2 ≤ n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 2) ↔ (2 ≤ n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 2) ↔ (2 ≤ n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 2) ↔ (2 ≤ n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 2) ↔ (2 ≤ n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 2) ↔ (2 ≤ n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 2) ↔ (2 ≤ n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 2) ↔ (2 ≤ n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 < n), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) →
    (∀ (n : ℕ) (hn : 3 < n), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) →
    (∀ (n : ℕ) (hn : 3 < n), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) →
    (∀ (n : ℕ) (hn : 3 < n), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) →
    (∀ (n : ℕ) (hn : 3 < n), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) →
    (∀ (n : ℕ) (hn : 3 < n), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) →
    (∀ (n : ℕ) (hn : 3 < n), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) →
    (∀ (n : ℕ) (hn : 3 < n), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 2) ↔ (3 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 2) ↔ (3 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 2) ↔ (3 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 2) ↔ (3 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 2) ↔ (3 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 2) ↔ (3 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (n > 2) ↔ (3 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 2) ↔ (3 < n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 2) ↔ (3 < n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 2) ↔ (3 < n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 2) ↔ (3 < n))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 2) ↔ (3 < n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 2) ↔ (3 < n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((n > 2) ↔ (3 < n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 2) ↔ (3 < n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 2) ↔ (3 < n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 2) ↔ (3 < n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 2) ↔ (3 < n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 2) ↔ (3 < n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 2) ↔ (3 < n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n > 2) ↔ (3 < n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 3), n ∣ (a (n - 1) + 3 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3), n ∣ (a (n - 1) + 3 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) →
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3), n ∣ (a (n - 1) + 3 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) →
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3), n ∣ (a (n - 1) + 3 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) →
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3), n ∣ (a (n - 1) + 3 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) →
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3), n ∣ (a (n - 1) + 3 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) →
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3), n ∣ (a (n - 1) + 3 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) →
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3), n ∣ (a (n - 1) + 3 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) →
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) →
    (∀ (n : ℕ) (hn : n ≥ 3), n ∣ (a (n - 1) + 3 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) →
    (∀ (n : ℕ) (hn : n ≥ 3), n ∣ (a (n - 1) + 3 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) →
    (∀ (n : ℕ) (hn : n ≥ 3), n ∣ (a (n - 1) + 3 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) →
    (∀ (n : ℕ) (hn : n ≥ 3), n ∣ (a (n - 1) + 3 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) →
    (∀ (n : ℕ) (hn : n ≥ 3), n ∣ (a (n - 1) + 3 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) →
    (∀ (n : ℕ) (hn : n ≥ 3), n ∣ (a (n - 1) + 3 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 2), n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) →
    (∀ (n : ℕ) (hn : n ≥ 3), n ∣ (a (n - 1) + 3 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n > 2) ∧ (¬(n ∣ (a (n - 1) + 3 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n > 2) ∧ (¬(n ∣ (a (n - 1) + 3 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n > 2) ∧ (¬(n ∣ (a (n - 1) + 3 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n > 2) ∧ (¬(n ∣ (a (n - 1) + 3 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n > 2) ∧ (¬(n ∣ (a (n - 1) + 3 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n > 2) ∧ (¬(n ∣ (a (n - 1) + 3 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n > 2) ∧ (¬(n ∣ (a (n - 1) + 3 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) ↔ (n ∣ (a (n - 1) + 3 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) ↔ (n ∣ (a (n - 1) + 3 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) ↔ (n ∣ (a (n - 1) + 3 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) ↔ (n ∣ (a (n - 1) + 3 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) ↔ (n ∣ (a (n - 1) + 3 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) ↔ (n ∣ (a (n - 1) + 3 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n)) ↔ (n ∣ (a (n - 1) + 3 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : n > 2) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : n > 2) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : n > 2) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : n > 2) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : n > 2) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
