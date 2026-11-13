import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Minimum modulus for the unique multiset-sum problem

*References:*
- [arxiv/2607.08366](https://arxiv.org/abs/2607.08366)
  **Minimum modulus for the unique multiset-sum problem**
  by *José A. R. Fonollosa*
- [jarfo/min-modulus](https://github.com/jarfo/min-modulus), the author's Lean development of
  the paper's Main Theorem. Section 7 of the paper describes it.

The paper's Main Theorem fixes the super-increasing set $\{2^k - 1\}$ and pins the least modulus
at which *it* is valid. Conjecture 1 says no other set of $n$ residues does better, and is open.
-/

section

open Finset

namespace Arxiv.«2607.08366»

variable {N : ℕ}

/-- `A` is *valid mod* `N` when the all-ones multiset is the only multiset of size `#A` drawn
from `A` whose sum matches `∑ a ∈ A, a`.

`m a` is how many copies of `a` the multiset uses. The all-ones multiset has `m a = 1` for
every `a ∈ A`; values outside `A` do not affect the sums. -/
def IsValidMod (A : Finset (ZMod N)) : Prop :=
  ∀ m : ZMod N → ℕ, ∑ a ∈ A, m a = #A → ∑ a ∈ A, (m a : ZMod N) * a = ∑ a ∈ A, a →
    ∀ a ∈ A, m a = 1

/-- The candidate least modulus admitting a valid set of `n` residues, conjecturally
$2^n - 2^{\lfloor\log_2 n\rfloor}$. -/
def minModulus (n : ℕ) : ℕ := 2 ^ n - 2 ^ (Nat.log 2 n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 < n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) →
    (∀ (n : ℕ) (hn : 2 < n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) →
    (∀ (n : ℕ) (hn : 2 < n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) →
    (∀ (n : ℕ) (hn : 2 < n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) →
    (∀ (n : ℕ) (hn : 2 < n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) →
    (∀ (n : ℕ) (hn : 2 < n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) →
    (∀ (n : ℕ) (hn : 2 < n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) →
    (∀ (n : ℕ) (hn : 2 < n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (2 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (2 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (2 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (2 < n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (2 < n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (2 < n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (2 < n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (2 < n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (2 < n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) →
    (∀ (n : ℕ) (hn : 3 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) →
    (∀ (n : ℕ) (hn : 3 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) →
    (∀ (n : ℕ) (hn : 3 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) →
    (∀ (n : ℕ) (hn : 3 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) →
    (∀ (n : ℕ) (hn : 3 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) →
    (∀ (n : ℕ) (hn : 3 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) →
    (∀ (n : ℕ) (hn : 3 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (3 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (3 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (3 ≤ n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (3 ≤ n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (3 ≤ n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (3 ≤ n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (3 ≤ n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (3 ≤ n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (3 ≤ n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (3 ≤ n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 2), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (n ≥ 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (n ≥ 2) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (n ≥ 2) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (n ≥ 2) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (n ≥ 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (n ≥ 2) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (n ≥ 2) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (n ≥ 2) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) ↔
    (∀ (n : ℕ) (hn : n ≥ 2), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) ↔
    (∀ (n : ℕ) (hn : n ≥ 2), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) ↔
    (∀ (n : ℕ) (hn : n ≥ 2), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) ↔
    (∀ (n : ℕ) (hn : n ≥ 2), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), ∃ A₁ : Finset (ZMod (minModulus n)), #A₁ = n ∧ IsValidMod A₁

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) ↔ (∃ A₁ : Finset (ZMod (minModulus n)), #A₁ = n ∧ IsValidMod A₁) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) ↔ (∃ A₁ : Finset (ZMod (minModulus n)), #A₁ = n ∧ IsValidMod A₁) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) ↔ (∃ A₁ : Finset (ZMod (minModulus n)), #A₁ = n ∧ IsValidMod A₁) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) ↔ (∃ A₁ : Finset (ZMod (minModulus n)), #A₁ = n ∧ IsValidMod A₁) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) ↔ (∃ A₁ : Finset (ZMod (minModulus n)), #A₁ = n ∧ IsValidMod A₁) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) ↔ (∃ A₁ : Finset (ZMod (minModulus n)), #A₁ = n ∧ IsValidMod A₁) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) ↔ (∃ A₁ : Finset (ZMod (minModulus n)), #A₁ = n ∧ IsValidMod A₁) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) ↔ (∃ A₁ : Finset (ZMod (minModulus n)), #A₁ = n ∧ IsValidMod A₁) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) ↔
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A₁ : Finset (ZMod (minModulus n)), #A₁ = n ∧ IsValidMod A₁) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) ↔
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A₁ : Finset (ZMod (minModulus n)), #A₁ = n ∧ IsValidMod A₁) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) ↔
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A₁ : Finset (ZMod (minModulus n)), #A₁ = n ∧ IsValidMod A₁) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) ↔
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A₁ : Finset (ZMod (minModulus n)), #A₁ = n ∧ IsValidMod A₁) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn₀ : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) ↔
    (∀ (n : ℕ) (hn₀ : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) ↔
    (∀ (n : ℕ) (hn₀ : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) ↔
    (∀ (n : ℕ) (hn₀ : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) ↔
    (∀ (n : ℕ) (hn₀ : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : ¬(n < 2)), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) ↔
    (∀ (n : ℕ) (hn : ¬(n < 2)), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) ↔
    (∀ (n : ℕ) (hn : ¬(n < 2)), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) ↔
    (∀ (n : ℕ) (hn : ¬(n < 2)), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) ↔
    (∀ (n : ℕ) (hn : ¬(n < 2)), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (1 < n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (1 < n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (1 < n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (1 < n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (1 < n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (1 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (1 < n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (1 < n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) ↔
    (∀ (n : ℕ) (hn : 1 < n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) ↔
    (∀ (n : ℕ) (hn : 1 < n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) ↔
    (∀ (n : ℕ) (hn : 1 < n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) ↔
    (∀ (n : ℕ) (hn : 1 < n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 2), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) →
    (∀ (n : ℕ) (hn : n > 2), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) →
    (∀ (n : ℕ) (hn : n > 2), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) →
    (∀ (n : ℕ) (hn : n > 2), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) →
    (∀ (n : ℕ) (hn : n > 2), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) →
    (∀ (n : ℕ) (hn : n > 2), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) →
    (∀ (n : ℕ) (hn : n > 2), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) →
    (∀ (n : ℕ) (hn : n > 2), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n > 2) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n > 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n > 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n > 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n > 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n > 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n > 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n > 2))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n > 2))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n > 2))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n > 2))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n > 2))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n > 2))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n > 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n > 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n > 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n > 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n > 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n > 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 3), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) →
    (∀ (n : ℕ) (hn : n ≥ 3), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) →
    (∀ (n : ℕ) (hn : n ≥ 3), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) →
    (∀ (n : ℕ) (hn : n ≥ 3), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) →
    (∀ (n : ℕ) (hn : n ≥ 3), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) →
    (∀ (n : ℕ) (hn : n ≥ 3), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) →
    (∀ (n : ℕ) (hn : n ≥ 3), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) →
    (∀ (n : ℕ) (hn : n ≥ 3), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n ≥ 3) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n ≥ 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n ≥ 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n ≥ 3))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n ≥ 3))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n ≥ 3))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n ≥ 3))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n ≥ 3))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n ≥ 3))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n ≥ 3))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n ≥ 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n ≥ 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n ≥ 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n ≥ 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n ≥ 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n ≥ 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n ≥ 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) →
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) →
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) →
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) →
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) →
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) →
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) →
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset (ZMod (minModulus n)), #A = n ∧ IsValidMod A) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (1 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (1 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (1 ≤ n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (1 ≤ n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (1 ≤ n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (1 ≤ n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (1 ≤ n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (1 ≤ n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (1 ≤ n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (1 ≤ n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (1 ≤ n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (1 ≤ n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (1 ≤ n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (1 ≤ n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (1 ≤ n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 2 ≤ n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 2 ≤ n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 2 ≤ n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 2 ≤ n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 2 ≤ n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
