import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Divisibility of $2^n + 1$ by $n$

A56777 lists composite numbers $n$ satisfying both $\varphi(n+12) = \varphi(n) + 12$ and
$\sigma(n+12) = \sigma(n) + 12$.

The conjectures state identities connecting A56777 and prime quadruples (A7530), as
well as congruences satisfied by the members of A56777.

*References:*
- [A56777](https://oeis.org/A56777)
-/

section

namespace OeisA56777

open Nat
open scoped ArithmeticFunction.sigma

/-- A composite number $n$ is in the sequence A56777 if it satisfies both
$\varphi(n+12) = \varphi(n) + 12$ and $\sigma(n+12) = \sigma(n) + 12$. -/
def A (n : ℕ) : Prop :=
  ¬n.Prime ∧ 1 < n ∧ totient (n + 12) = totient n + 12 ∧ σ 1 (n + 12) = σ 1 n + 12

/-- A number $n$ comes from a prime quadruple $(p, p+2, p+6, p+8)$ if
$n = p(p+8)$ for some prime $p$ where $p$, $p+2$, $p+6$, $p+8$ are all prime. -/
def ComesFromPrimeQuadruple (n : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ (p + 2).Prime ∧ (p + 6).Prime ∧ (p + 8).Prime ∧ n = p * (p + 8)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h : ComesFromPrimeQuadruple n), n % 100 = 9

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : ComesFromPrimeQuadruple n), n % 100 = 9) →
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : ComesFromPrimeQuadruple n), n % 100 = 9) →
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : ComesFromPrimeQuadruple n), n % 100 = 9) →
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : ComesFromPrimeQuadruple n), n % 100 = 9) →
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : ComesFromPrimeQuadruple n), n % 100 = 9) →
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : ComesFromPrimeQuadruple n), n % 100 = 9) →
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h : ComesFromPrimeQuadruple n), n % 100 = 9) →
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ} (h : ComesFromPrimeQuadruple n) :
    (65 < n) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (h : ComesFromPrimeQuadruple n) :
    (65 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ} (h : ComesFromPrimeQuadruple n) :
    (65 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (h : ComesFromPrimeQuadruple n) :
    (65 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (h : ComesFromPrimeQuadruple n) :
    (65 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ} (h : ComesFromPrimeQuadruple n) :
    (65 < n) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} (h : ComesFromPrimeQuadruple n) :
    (65 < n) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (ComesFromPrimeQuadruple n) ∧ (¬((65 < n) ↔ (True))) :=
  ⟨(65 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (ComesFromPrimeQuadruple n) ∧ (¬((65 < n) ↔ (True))) :=
  ⟨(64 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (ComesFromPrimeQuadruple n) ∧ (¬((65 < n) ↔ (True))) :=
  ⟨(66 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (ComesFromPrimeQuadruple n) ∧ (¬((65 < n) ↔ (True))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (ComesFromPrimeQuadruple n) ∧ (¬((65 < n) ↔ (True))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (ComesFromPrimeQuadruple n) ∧ (¬((65 < n) ↔ (True))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (ComesFromPrimeQuadruple n) ∧ (¬((65 < n) ↔ (True))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (ComesFromPrimeQuadruple n) ∧ (¬((65 < n) ↔ (True))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (ComesFromPrimeQuadruple n) ∧ (¬((65 < n) ↔ (True))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((65 < n) ↔ (True)) :=
  ⟨(65 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((65 < n) ↔ (True)) :=
  ⟨(64 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((65 < n) ↔ (True)) :=
  ⟨(66 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((65 < n) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((65 < n) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((65 < n) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((65 < n) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((65 < n) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((65 < n) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h65 : 66 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) →
    (∀ {n : ℕ} (h65 : 66 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) →
    (∀ {n : ℕ} (h65 : 66 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) →
    (∀ {n : ℕ} (h65 : 66 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) →
    (∀ {n : ℕ} (h65 : 66 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) →
    (∀ {n : ℕ} (h65 : 66 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) →
    (∀ {n : ℕ} (h65 : 66 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) →
    (∀ {n : ℕ} (h65 : 66 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ} (h : ComesFromPrimeQuadruple n) :
    (65 < n) ↔ (66 < n) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (h : ComesFromPrimeQuadruple n) :
    (65 < n) ↔ (66 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ} (h : ComesFromPrimeQuadruple n) :
    (65 < n) ↔ (66 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (h : ComesFromPrimeQuadruple n) :
    (65 < n) ↔ (66 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (h : ComesFromPrimeQuadruple n) :
    (65 < n) ↔ (66 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ} (h : ComesFromPrimeQuadruple n) :
    (65 < n) ↔ (66 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} (h : ComesFromPrimeQuadruple n) :
    (65 < n) ↔ (66 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (ComesFromPrimeQuadruple n) ∧ (¬((65 < n) ↔ (66 < n))) :=
  ⟨(65 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (ComesFromPrimeQuadruple n) ∧ (¬((65 < n) ↔ (66 < n))) :=
  ⟨(64 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (ComesFromPrimeQuadruple n) ∧ (¬((65 < n) ↔ (66 < n))) :=
  ⟨(66 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (ComesFromPrimeQuadruple n) ∧ (¬((65 < n) ↔ (66 < n))) :=
  ⟨(67 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (ComesFromPrimeQuadruple n) ∧ (¬((65 < n) ↔ (66 < n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (ComesFromPrimeQuadruple n) ∧ (¬((65 < n) ↔ (66 < n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (ComesFromPrimeQuadruple n) ∧ (¬((65 < n) ↔ (66 < n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (ComesFromPrimeQuadruple n) ∧ (¬((65 < n) ↔ (66 < n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (ComesFromPrimeQuadruple n) ∧ (¬((65 < n) ↔ (66 < n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (ComesFromPrimeQuadruple n) ∧ (¬((65 < n) ↔ (66 < n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((65 < n) ↔ (66 < n)) :=
  ⟨(65 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((65 < n) ↔ (66 < n)) :=
  ⟨(64 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((65 < n) ↔ (66 < n)) :=
  ⟨(66 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((65 < n) ↔ (66 < n)) :=
  ⟨(67 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((65 < n) ↔ (66 < n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((65 < n) ↔ (66 < n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((65 < n) ↔ (66 < n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((65 < n) ↔ (66 < n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((65 < n) ↔ (66 < n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((65 < n) ↔ (66 < n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h65 : n > 65) (h : ComesFromPrimeQuadruple n), n % 100 = 9

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (65 < n) ↔ (n > 65) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (65 < n) ↔ (n > 65) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (65 < n) ↔ (n > 65) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (65 < n) ↔ (n > 65) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (65 < n) ↔ (n > 65) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (65 < n) ↔ (n > 65) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (65 < n) ↔ (n > 65) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (65 < n) ↔ (n > 65) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) ↔
    (∀ {n : ℕ} (h65 : n > 65) (h : ComesFromPrimeQuadruple n), n % 100 = 9) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) ↔
    (∀ {n : ℕ} (h65 : n > 65) (h : ComesFromPrimeQuadruple n), n % 100 = 9) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) ↔
    (∀ {n : ℕ} (h65 : n > 65) (h : ComesFromPrimeQuadruple n), n % 100 = 9) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) ↔
    (∀ {n : ℕ} (h65 : n > 65) (h : ComesFromPrimeQuadruple n), n % 100 = 9) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h : ComesFromPrimeQuadruple n) (h65 : 65 < n), n % 100 = 9

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) ↔
    (∀ {n : ℕ} (h : ComesFromPrimeQuadruple n) (h65 : 65 < n), n % 100 = 9) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) ↔
    (∀ {n : ℕ} (h : ComesFromPrimeQuadruple n) (h65 : 65 < n), n % 100 = 9) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) ↔
    (∀ {n : ℕ} (h : ComesFromPrimeQuadruple n) (h65 : 65 < n), n % 100 = 9) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) ↔
    (∀ {n : ℕ} (h : ComesFromPrimeQuadruple n) (h65 : 65 < n), n % 100 = 9) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h65' : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) ↔
    (∀ {n : ℕ} (h65' : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) ↔
    (∀ {n : ℕ} (h65' : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) ↔
    (∀ {n : ℕ} (h65' : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) ↔
    (∀ {n : ℕ} (h65' : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h65 : ¬(n ≤ 65)) (h : ComesFromPrimeQuadruple n), n % 100 = 9

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (65 < n) ↔ (¬(n ≤ 65)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (65 < n) ↔ (¬(n ≤ 65)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (65 < n) ↔ (¬(n ≤ 65)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (65 < n) ↔ (¬(n ≤ 65)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (65 < n) ↔ (¬(n ≤ 65)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (65 < n) ↔ (¬(n ≤ 65)) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (65 < n) ↔ (¬(n ≤ 65)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (65 < n) ↔ (¬(n ≤ 65)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) ↔
    (∀ {n : ℕ} (h65 : ¬(n ≤ 65)) (h : ComesFromPrimeQuadruple n), n % 100 = 9) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) ↔
    (∀ {n : ℕ} (h65 : ¬(n ≤ 65)) (h : ComesFromPrimeQuadruple n), n % 100 = 9) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) ↔
    (∀ {n : ℕ} (h65 : ¬(n ≤ 65)) (h : ComesFromPrimeQuadruple n), n % 100 = 9) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) ↔
    (∀ {n : ℕ} (h65 : ¬(n ≤ 65)) (h : ComesFromPrimeQuadruple n), n % 100 = 9) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h65 : 66 ≤ n) (h : ComesFromPrimeQuadruple n), n % 100 = 9

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (65 < n) ↔ (66 ≤ n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (65 < n) ↔ (66 ≤ n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (65 < n) ↔ (66 ≤ n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (65 < n) ↔ (66 ≤ n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (65 < n) ↔ (66 ≤ n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (65 < n) ↔ (66 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (65 < n) ↔ (66 ≤ n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (65 < n) ↔ (66 ≤ n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) ↔
    (∀ {n : ℕ} (h65 : 66 ≤ n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) ↔
    (∀ {n : ℕ} (h65 : 66 ≤ n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) ↔
    (∀ {n : ℕ} (h65 : 66 ≤ n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) ↔
    (∀ {n : ℕ} (h65 : 66 ≤ n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h65 : n > 66) (h : ComesFromPrimeQuadruple n), n % 100 = 9

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) →
    (∀ {n : ℕ} (h65 : n > 66) (h : ComesFromPrimeQuadruple n), n % 100 = 9) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) →
    (∀ {n : ℕ} (h65 : n > 66) (h : ComesFromPrimeQuadruple n), n % 100 = 9) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) →
    (∀ {n : ℕ} (h65 : n > 66) (h : ComesFromPrimeQuadruple n), n % 100 = 9) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) →
    (∀ {n : ℕ} (h65 : n > 66) (h : ComesFromPrimeQuadruple n), n % 100 = 9) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) →
    (∀ {n : ℕ} (h65 : n > 66) (h : ComesFromPrimeQuadruple n), n % 100 = 9) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) →
    (∀ {n : ℕ} (h65 : n > 66) (h : ComesFromPrimeQuadruple n), n % 100 = 9) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) →
    (∀ {n : ℕ} (h65 : n > 66) (h : ComesFromPrimeQuadruple n), n % 100 = 9) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ} (h : ComesFromPrimeQuadruple n) :
    (65 < n) ↔ (n > 66) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (h : ComesFromPrimeQuadruple n) :
    (65 < n) ↔ (n > 66) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ} (h : ComesFromPrimeQuadruple n) :
    (65 < n) ↔ (n > 66) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (h : ComesFromPrimeQuadruple n) :
    (65 < n) ↔ (n > 66) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (h : ComesFromPrimeQuadruple n) :
    (65 < n) ↔ (n > 66) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ} (h : ComesFromPrimeQuadruple n) :
    (65 < n) ↔ (n > 66) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} (h : ComesFromPrimeQuadruple n) :
    (65 < n) ↔ (n > 66) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (ComesFromPrimeQuadruple n) ∧ (¬((65 < n) ↔ (n > 66))) :=
  ⟨(65 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (ComesFromPrimeQuadruple n) ∧ (¬((65 < n) ↔ (n > 66))) :=
  ⟨(64 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (ComesFromPrimeQuadruple n) ∧ (¬((65 < n) ↔ (n > 66))) :=
  ⟨(66 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (ComesFromPrimeQuadruple n) ∧ (¬((65 < n) ↔ (n > 66))) :=
  ⟨(67 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (ComesFromPrimeQuadruple n) ∧ (¬((65 < n) ↔ (n > 66))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (ComesFromPrimeQuadruple n) ∧ (¬((65 < n) ↔ (n > 66))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (ComesFromPrimeQuadruple n) ∧ (¬((65 < n) ↔ (n > 66))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (ComesFromPrimeQuadruple n) ∧ (¬((65 < n) ↔ (n > 66))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (ComesFromPrimeQuadruple n) ∧ (¬((65 < n) ↔ (n > 66))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (ComesFromPrimeQuadruple n) ∧ (¬((65 < n) ↔ (n > 66))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((65 < n) ↔ (n > 66)) :=
  ⟨(65 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((65 < n) ↔ (n > 66)) :=
  ⟨(64 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((65 < n) ↔ (n > 66)) :=
  ⟨(66 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((65 < n) ↔ (n > 66)) :=
  ⟨(67 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((65 < n) ↔ (n > 66)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((65 < n) ↔ (n > 66)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((65 < n) ↔ (n > 66)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((65 < n) ↔ (n > 66)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((65 < n) ↔ (n > 66)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((65 < n) ↔ (n > 66)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (h65 : 66 ≤ n) (h : ComesFromPrimeQuadruple n), n % 101 = 9

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 66 ≤ n) (h : ComesFromPrimeQuadruple n), n % 101 = 9) →
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 66 ≤ n) (h : ComesFromPrimeQuadruple n), n % 101 = 9) →
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 66 ≤ n) (h : ComesFromPrimeQuadruple n), n % 101 = 9) →
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 66 ≤ n) (h : ComesFromPrimeQuadruple n), n % 101 = 9) →
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 66 ≤ n) (h : ComesFromPrimeQuadruple n), n % 101 = 9) →
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 66 ≤ n) (h : ComesFromPrimeQuadruple n), n % 101 = 9) →
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 66 ≤ n) (h : ComesFromPrimeQuadruple n), n % 101 = 9) →
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) →
    (∀ {n : ℕ} (h65 : 66 ≤ n) (h : ComesFromPrimeQuadruple n), n % 101 = 9) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) →
    (∀ {n : ℕ} (h65 : 66 ≤ n) (h : ComesFromPrimeQuadruple n), n % 101 = 9) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) →
    (∀ {n : ℕ} (h65 : 66 ≤ n) (h : ComesFromPrimeQuadruple n), n % 101 = 9) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) →
    (∀ {n : ℕ} (h65 : 66 ≤ n) (h : ComesFromPrimeQuadruple n), n % 101 = 9) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) →
    (∀ {n : ℕ} (h65 : 66 ≤ n) (h : ComesFromPrimeQuadruple n), n % 101 = 9) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) →
    (∀ {n : ℕ} (h65 : 66 ≤ n) (h : ComesFromPrimeQuadruple n), n % 101 = 9) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n), n % 100 = 9) →
    (∀ {n : ℕ} (h65 : 66 ≤ n) (h : ComesFromPrimeQuadruple n), n % 101 = 9) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (65 < n) ∧ (ComesFromPrimeQuadruple n) ∧ (¬(n % 101 = 9)) :=
  ⟨(65 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (65 < n) ∧ (ComesFromPrimeQuadruple n) ∧ (¬(n % 101 = 9)) :=
  ⟨(64 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (65 < n) ∧ (ComesFromPrimeQuadruple n) ∧ (¬(n % 101 = 9)) :=
  ⟨(66 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (65 < n) ∧ (ComesFromPrimeQuadruple n) ∧ (¬(n % 101 = 9)) :=
  ⟨(101 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (65 < n) ∧ (ComesFromPrimeQuadruple n) ∧ (¬(n % 101 = 9)) :=
  ⟨(100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (65 < n) ∧ (ComesFromPrimeQuadruple n) ∧ (¬(n % 101 = 9)) :=
  ⟨(102 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (65 < n) ∧ (ComesFromPrimeQuadruple n) ∧ (¬(n % 101 = 9)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (65 < n) ∧ (ComesFromPrimeQuadruple n) ∧ (¬(n % 101 = 9)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (65 < n) ∧ (ComesFromPrimeQuadruple n) ∧ (¬(n % 101 = 9)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (65 < n) ∧ (ComesFromPrimeQuadruple n) ∧ (¬(n % 101 = 9)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (65 < n) ∧ (ComesFromPrimeQuadruple n) ∧ (¬(n % 101 = 9)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (65 < n) ∧ (ComesFromPrimeQuadruple n) ∧ (¬(n % 101 = 9)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (65 < n) ∧ (ComesFromPrimeQuadruple n) ∧ (¬(n % 101 = 9)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (65 < n) ∧ (ComesFromPrimeQuadruple n) ∧ (¬(n % 101 = 9)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n % 100 = 9) ↔ (n % 101 = 9)) :=
  ⟨(100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n % 100 = 9) ↔ (n % 101 = 9)) :=
  ⟨(99 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n % 100 = 9) ↔ (n % 101 = 9)) :=
  ⟨(101 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n % 100 = 9) ↔ (n % 101 = 9)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n % 100 = 9) ↔ (n % 101 = 9)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n % 100 = 9) ↔ (n % 101 = 9)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n % 100 = 9) ↔ (n % 101 = 9)) :=
  ⟨(102 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n % 100 = 9) ↔ (n % 101 = 9)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n % 100 = 9) ↔ (n % 101 = 9)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n % 100 = 9) ↔ (n % 101 = 9)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n % 100 = 9) ↔ (n % 101 = 9)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n % 100 = 9) ↔ (n % 101 = 9)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
