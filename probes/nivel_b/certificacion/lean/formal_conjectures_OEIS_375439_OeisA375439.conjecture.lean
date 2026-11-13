import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# A cubic generating function with ternary substitution

The coefficients of the generating function
$A(x)=x+x^2+(2A(x)^3+A(x^3))/3$, with constant term $a(0)=0$.

*References:*
- [A375439](https://oeis.org/A375439)
- [A038754](https://oeis.org/A038754)
- [Li26] Wentao Li, [Parity of A375439](https://github.com/VictorLiwentao/lean-oeis-proofs/blob/0a23974e54b90afd1453ef02c27cf8f617bad940/proofs/new-proofs/A375439/PROOF.md), 2026.
-/

section

namespace OeisA375439

/-- Coefficients of the square of a power series with coefficient sequence $b$. -/
def conv2 (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), b k * b (n - k)

/-- Coefficients of the cube of a power series with coefficient sequence $b$. -/
def conv3 (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), conv2 b k * b (n - k)

/-- Coefficients obtained by substituting $x^3$ for $x$. -/
def subst3 (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  if 3 ∣ n then b (n / 3) else 0

/-- Coefficients of $2B(x)^3+B(x^3)$. -/
def rhs (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  2 * conv3 b n + subst3 b n

/-- Coefficients of $A(x)=x+x^2+(2A(x)^3+A(x^3))/3$, with $a(0)=0$. -/
def a : ℕ → ℕ :=
  Nat.strongRec fun n ih =>
    if n = 0 then 0
    else if n = 1 then 1
    else if n = 2 then 1
    else
      let b : ℕ → ℕ := fun m => if h : m < n then ih m h else 0
      rhs b n / 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔ (Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔ (Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔ (Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔ (Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔ (Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔ (Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔ (Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 1), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (n ≥ 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (n ≥ 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (n ≥ 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (n ≥ 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (n ≥ 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (n ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (n ≥ 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (n ≥ 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔
    (∀ (n : ℕ) (hn : n ≥ 1), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔
    (∀ (n : ℕ) (hn : n ≥ 1), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔
    (∀ (n : ℕ) (hn : n ≥ 1), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔
    (∀ (n : ℕ) (hn : n ≥ 1), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k₁ : ℕ, n = 3 ^ k₁ ∨ n = 2 * 3 ^ k₁

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔ (Odd (a n) ↔ ∃ k₁ : ℕ, n = 3 ^ k₁ ∨ n = 2 * 3 ^ k₁) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔ (Odd (a n) ↔ ∃ k₁ : ℕ, n = 3 ^ k₁ ∨ n = 2 * 3 ^ k₁) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔ (Odd (a n) ↔ ∃ k₁ : ℕ, n = 3 ^ k₁ ∨ n = 2 * 3 ^ k₁) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔ (Odd (a n) ↔ ∃ k₁ : ℕ, n = 3 ^ k₁ ∨ n = 2 * 3 ^ k₁) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔ (Odd (a n) ↔ ∃ k₁ : ℕ, n = 3 ^ k₁ ∨ n = 2 * 3 ^ k₁) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔ (Odd (a n) ↔ ∃ k₁ : ℕ, n = 3 ^ k₁ ∨ n = 2 * 3 ^ k₁) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔ (Odd (a n) ↔ ∃ k₁ : ℕ, n = 3 ^ k₁ ∨ n = 2 * 3 ^ k₁) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔ (Odd (a n) ↔ ∃ k₁ : ℕ, n = 3 ^ k₁ ∨ n = 2 * 3 ^ k₁) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k₁ : ℕ, n = 3 ^ k₁ ∨ n = 2 * 3 ^ k₁) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k₁ : ℕ, n = 3 ^ k₁ ∨ n = 2 * 3 ^ k₁) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k₁ : ℕ, n = 3 ^ k₁ ∨ n = 2 * 3 ^ k₁) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k₁ : ℕ, n = 3 ^ k₁ ∨ n = 2 * 3 ^ k₁) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn₀ : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔
    (∀ (n : ℕ) (hn₀ : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔
    (∀ (n : ℕ) (hn₀ : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔
    (∀ (n : ℕ) (hn₀ : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔
    (∀ (n : ℕ) (hn₀ : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : ¬(n < 1)), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔
    (∀ (n : ℕ) (hn : ¬(n < 1)), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔
    (∀ (n : ℕ) (hn : ¬(n < 1)), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔
    (∀ (n : ℕ) (hn : ¬(n < 1)), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔
    (∀ (n : ℕ) (hn : ¬(n < 1)), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (0 < n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (0 < n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (0 < n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (0 < n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (0 < n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (0 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (0 < n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (0 < n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔
    (∀ (n : ℕ) (hn : 0 < n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔
    (∀ (n : ℕ) (hn : 0 < n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔
    (∀ (n : ℕ) (hn : 0 < n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔
    (∀ (n : ℕ) (hn : 0 < n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 1), Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) →
    (∀ (n : ℕ) (hn : n ≥ 1), Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) →
    (∀ (n : ℕ) (hn : n ≥ 1), Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) →
    (∀ (n : ℕ) (hn : n ≥ 1), Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) →
    (∀ (n : ℕ) (hn : n ≥ 1), Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) →
    (∀ (n : ℕ) (hn : n ≥ 1), Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) →
    (∀ (n : ℕ) (hn : n ≥ 1), Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) →
    (∀ (n : ℕ) (hn : n ≥ 1), Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔ (Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔ (Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔ (Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔ (Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔ (Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔ (Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔ (Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) →
    (∀ (n : ℕ) (hn : 0 < n), Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) →
    (∀ (n : ℕ) (hn : 0 < n), Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) →
    (∀ (n : ℕ) (hn : 0 < n), Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) →
    (∀ (n : ℕ) (hn : 0 < n), Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) →
    (∀ (n : ℕ) (hn : 0 < n), Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) →
    (∀ (n : ℕ) (hn : 0 < n), Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) →
    (∀ (n : ℕ) (hn : 0 < n), Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔ (Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔ (Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔ (Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔ (Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔ (Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔ (Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Odd (a n) ↔ ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k) ↔ (Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k ∨ n = 2 * 3 ^ k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 ≤ n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 ≤ n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 ≤ n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 ≤ n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 ≤ n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
