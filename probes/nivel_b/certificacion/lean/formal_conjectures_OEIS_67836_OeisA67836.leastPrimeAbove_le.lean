import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Euclid–Fortunate prime coverage

OEIS A067836 starts with $2$. Each later term is the gap from the product of all previous terms to
the least prime strictly greater than that product plus one.

*References:*
- [OEIS A067836](https://oeis.org/A067836)
-/

section

namespace OeisA67836

/-- The finite set in which the least prime strictly above `n` is sought. -/
def primeCandidates (n : ℕ) : Finset ℕ :=
  (Finset.Icc (n + 1) (2 * (n + 1))).filter Nat.Prime

/-- Bertrand's postulate makes the finite prime-candidate set nonempty. -/
lemma primeCandidates_nonempty (n : ℕ) : (primeCandidates n).Nonempty := by
  obtain ⟨p, hp, hnp, hp_le⟩ := Nat.bertrand (n + 1) (by omega)
  refine ⟨p, ?_⟩
  simp only [primeCandidates, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨by omega, hp_le⟩, hp⟩

/-- The least prime strictly greater than `n`, found in the Bertrand interval. -/
def leastPrimeAbove (n : ℕ) : ℕ :=
  (primeCandidates n).min' (primeCandidates_nonempty n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hp : p.Prime), leastPrimeAbove n ≤ p

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime), leastPrimeAbove n ≤ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime), leastPrimeAbove n ≤ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime), leastPrimeAbove n ≤ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime), leastPrimeAbove n ≤ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime), leastPrimeAbove n ≤ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime), leastPrimeAbove n ≤ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hp : p.Prime), leastPrimeAbove n ≤ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (n < p) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (n < p) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (n < p) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (n < p) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (n < p) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (n < p) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (n < p) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (True))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (True))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (True))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (True))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (True))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (True))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (True))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (True))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (True))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (True))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (True))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (True))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (True))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (True))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (True))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (True))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (True))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (True))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (True))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (True)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (True)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (True)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (True)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (True)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (True)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (True)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (True)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (True)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (True)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (True)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (True)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (True)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (True)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (True)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (True)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (True)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (True)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (True)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (True)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (True)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (True)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (True)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (True)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (True)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (True)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (True)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (True)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (True)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (True)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (True)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (True)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n < p

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n < p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n < p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n < p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n < p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n < p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n < p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n < p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hnp : n ≤ p) (hp : p.Prime), leastPrimeAbove n ≤ p

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n ≤ p) (hp : p.Prime), leastPrimeAbove n ≤ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n ≤ p) (hp : p.Prime), leastPrimeAbove n ≤ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n ≤ p) (hp : p.Prime), leastPrimeAbove n ≤ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n ≤ p) (hp : p.Prime), leastPrimeAbove n ≤ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n ≤ p) (hp : p.Prime), leastPrimeAbove n ≤ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n ≤ p) (hp : p.Prime), leastPrimeAbove n ≤ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n ≤ p) (hp : p.Prime), leastPrimeAbove n ≤ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (n < p) ↔ (n ≤ p) := by
  omega

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (n < p) ↔ (n ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (n < p) ↔ (n ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (n < p) ↔ (n ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (n < p) ↔ (n ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (n < p) ↔ (n ≤ p) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (n < p) ↔ (n ≤ p) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≥ p

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≥ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≥ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≥ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≥ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≥ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≥ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≥ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≥ p) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≥ p) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≥ p) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≥ p) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≥ p) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≥ p) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≥ p) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hnp : p > n) (hp : p.Prime), leastPrimeAbove n ≤ p

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (n < p) ↔ (p > n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (n < p) ↔ (p > n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (n < p) ↔ (p > n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (n < p) ↔ (p > n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (n < p) ↔ (p > n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (n < p) ↔ (p > n) := by
  omega

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (n < p) ↔ (p > n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (n < p) ↔ (p > n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) ↔
    (∀ (n p : ℕ) (hnp : p > n) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) ↔
    (∀ (n p : ℕ) (hnp : p > n) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) ↔
    (∀ (n p : ℕ) (hnp : p > n) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) ↔
    (∀ (n p : ℕ) (hnp : p > n) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), p ≥ leastPrimeAbove n

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (leastPrimeAbove n ≤ p) ↔ (p ≥ leastPrimeAbove n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (leastPrimeAbove n ≤ p) ↔ (p ≥ leastPrimeAbove n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (leastPrimeAbove n ≤ p) ↔ (p ≥ leastPrimeAbove n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (leastPrimeAbove n ≤ p) ↔ (p ≥ leastPrimeAbove n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (leastPrimeAbove n ≤ p) ↔ (p ≥ leastPrimeAbove n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (leastPrimeAbove n ≤ p) ↔ (p ≥ leastPrimeAbove n) := by
  omega

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (leastPrimeAbove n ≤ p) ↔ (p ≥ leastPrimeAbove n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (leastPrimeAbove n ≤ p) ↔ (p ≥ leastPrimeAbove n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) ↔
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), p ≥ leastPrimeAbove n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) ↔
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), p ≥ leastPrimeAbove n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) ↔
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), p ≥ leastPrimeAbove n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) ↔
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), p ≥ leastPrimeAbove n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hp : p.Prime) (hnp : n < p), leastPrimeAbove n ≤ p

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) ↔
    (∀ (n p : ℕ) (hp : p.Prime) (hnp : n < p), leastPrimeAbove n ≤ p) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) ↔
    (∀ (n p : ℕ) (hp : p.Prime) (hnp : n < p), leastPrimeAbove n ≤ p) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) ↔
    (∀ (n p : ℕ) (hp : p.Prime) (hnp : n < p), leastPrimeAbove n ≤ p) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) ↔
    (∀ (n p : ℕ) (hp : p.Prime) (hnp : n < p), leastPrimeAbove n ≤ p) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hnp₀ : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) ↔
    (∀ (n p : ℕ) (hnp₀ : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) ↔
    (∀ (n p : ℕ) (hnp₀ : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) ↔
    (∀ (n p : ℕ) (hnp₀ : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) ↔
    (∀ (n p : ℕ) (hnp₀ : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hnp : ¬(p ≤ n)) (hp : p.Prime), leastPrimeAbove n ≤ p

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (n < p) ↔ (¬(p ≤ n)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (n < p) ↔ (¬(p ≤ n)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (n < p) ↔ (¬(p ≤ n)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (n < p) ↔ (¬(p ≤ n)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (n < p) ↔ (¬(p ≤ n)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (n < p) ↔ (¬(p ≤ n)) := by
  omega

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (n < p) ↔ (¬(p ≤ n)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n p : ℕ) :
    (n < p) ↔ (¬(p ≤ n)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) ↔
    (∀ (n p : ℕ) (hnp : ¬(p ≤ n)) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) ↔
    (∀ (n p : ℕ) (hnp : ¬(p ≤ n)) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) ↔
    (∀ (n p : ℕ) (hnp : ¬(p ≤ n)) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) ↔
    (∀ (n p : ℕ) (hnp : ¬(p ≤ n)) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hnp : p > n) (hp : p.Prime), leastPrimeAbove n < p

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : p > n) (hp : p.Prime), leastPrimeAbove n < p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : p > n) (hp : p.Prime), leastPrimeAbove n < p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : p > n) (hp : p.Prime), leastPrimeAbove n < p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : p > n) (hp : p.Prime), leastPrimeAbove n < p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : p > n) (hp : p.Prime), leastPrimeAbove n < p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : p > n) (hp : p.Prime), leastPrimeAbove n < p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : p > n) (hp : p.Prime), leastPrimeAbove n < p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n < p)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n < p)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hnp : p ≥ n) (hp : p.Prime), leastPrimeAbove n ≤ p

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : p ≥ n) (hp : p.Prime), leastPrimeAbove n ≤ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : p ≥ n) (hp : p.Prime), leastPrimeAbove n ≤ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : p ≥ n) (hp : p.Prime), leastPrimeAbove n ≤ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : p ≥ n) (hp : p.Prime), leastPrimeAbove n ≤ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : p ≥ n) (hp : p.Prime), leastPrimeAbove n ≤ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : p ≥ n) (hp : p.Prime), leastPrimeAbove n ≤ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : p ≥ n) (hp : p.Prime), leastPrimeAbove n ≤ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (n < p) ↔ (p ≥ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (n < p) ↔ (p ≥ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (n < p) ↔ (p ≥ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (n < p) ↔ (p ≥ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (n < p) ↔ (p ≥ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (n < p) ↔ (p ≥ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (n < p) ↔ (p ≥ n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (p ≥ n))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (p ≥ n))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (p ≥ n))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (p ≥ n))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (p ≥ n))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (p ≥ n))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (p ≥ n))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (p ≥ n))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (p ≥ n))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (p ≥ n))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (p ≥ n))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (p ≥ n))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (p ≥ n))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (p ≥ n))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (p ≥ n))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (p ≥ n))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (p ≥ n))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (p ≥ n))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (p ≥ n))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (p ≥ n))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (p ≥ n))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (p ≥ n))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (p ≥ n))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (p ≥ n))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (p ≥ n))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (p ≥ n))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (p ≥ n))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (p ≥ n))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (p ≥ n))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (p ≥ n))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (p ≥ n))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (p ≥ n))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (p ≥ n)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (p ≥ n)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (p ≥ n)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (p ≥ n)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (p ≥ n)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (p ≥ n)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (p ≥ n)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (p ≥ n)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (p ≥ n)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (p ≥ n)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (p ≥ n)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (p ≥ n)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (p ≥ n)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (p ≥ n)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (p ≥ n)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (p ≥ n)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (p ≥ n)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (p ≥ n)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (p ≥ n)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (p ≥ n)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (p ≥ n)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (p ≥ n)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (p ≥ n)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (p ≥ n)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (p ≥ n)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (p ≥ n)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (p ≥ n)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (p ≥ n)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (p ≥ n)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (p ≥ n)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (p ≥ n)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (p ≥ n)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hnp : p > n) (hp : p.Prime), leastPrimeAbove n ≥ p

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : p > n) (hp : p.Prime), leastPrimeAbove n ≥ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : p > n) (hp : p.Prime), leastPrimeAbove n ≥ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : p > n) (hp : p.Prime), leastPrimeAbove n ≥ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : p > n) (hp : p.Prime), leastPrimeAbove n ≥ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : p > n) (hp : p.Prime), leastPrimeAbove n ≥ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : p > n) (hp : p.Prime), leastPrimeAbove n ≥ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : p > n) (hp : p.Prime), leastPrimeAbove n ≥ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) →
    (∀ (n p : ℕ) (hnp : p > n) (hp : p.Prime), leastPrimeAbove n ≥ p) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) →
    (∀ (n p : ℕ) (hnp : p > n) (hp : p.Prime), leastPrimeAbove n ≥ p) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) →
    (∀ (n p : ℕ) (hnp : p > n) (hp : p.Prime), leastPrimeAbove n ≥ p) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) →
    (∀ (n p : ℕ) (hnp : p > n) (hp : p.Prime), leastPrimeAbove n ≥ p) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) →
    (∀ (n p : ℕ) (hnp : p > n) (hp : p.Prime), leastPrimeAbove n ≥ p) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) →
    (∀ (n p : ℕ) (hnp : p > n) (hp : p.Prime), leastPrimeAbove n ≥ p) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) →
    (∀ (n p : ℕ) (hnp : p > n) (hp : p.Prime), leastPrimeAbove n ≥ p) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(leastPrimeAbove n ≥ p)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (leastPrimeAbove n ≥ p)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), p > leastPrimeAbove n

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), p > leastPrimeAbove n) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), p > leastPrimeAbove n) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), p > leastPrimeAbove n) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), p > leastPrimeAbove n) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), p > leastPrimeAbove n) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), p > leastPrimeAbove n) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), p > leastPrimeAbove n) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p > leastPrimeAbove n)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p > leastPrimeAbove n)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p > leastPrimeAbove n)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p > leastPrimeAbove n)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p > leastPrimeAbove n)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p > leastPrimeAbove n)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p > leastPrimeAbove n)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p > leastPrimeAbove n)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p > leastPrimeAbove n)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p > leastPrimeAbove n)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p > leastPrimeAbove n)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p > leastPrimeAbove n)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p > leastPrimeAbove n)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p > leastPrimeAbove n)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p > leastPrimeAbove n)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p > leastPrimeAbove n)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p > leastPrimeAbove n)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p > leastPrimeAbove n)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p > leastPrimeAbove n)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p > leastPrimeAbove n)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p > leastPrimeAbove n)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p > leastPrimeAbove n)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p > leastPrimeAbove n)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p > leastPrimeAbove n)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p > leastPrimeAbove n)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p > leastPrimeAbove n)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p > leastPrimeAbove n)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p > leastPrimeAbove n)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p > leastPrimeAbove n)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p > leastPrimeAbove n)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p > leastPrimeAbove n)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p > leastPrimeAbove n)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p > leastPrimeAbove n)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p > leastPrimeAbove n)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p > leastPrimeAbove n)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p > leastPrimeAbove n)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p > leastPrimeAbove n)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p > leastPrimeAbove n)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p > leastPrimeAbove n)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p > leastPrimeAbove n)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p > leastPrimeAbove n)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p > leastPrimeAbove n)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p > leastPrimeAbove n)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p > leastPrimeAbove n)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p > leastPrimeAbove n)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p > leastPrimeAbove n)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p > leastPrimeAbove n)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p > leastPrimeAbove n)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p > leastPrimeAbove n)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p > leastPrimeAbove n)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p > leastPrimeAbove n)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p > leastPrimeAbove n)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p > leastPrimeAbove n)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p > leastPrimeAbove n)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p > leastPrimeAbove n)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p > leastPrimeAbove n)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p > leastPrimeAbove n)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p > leastPrimeAbove n)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p > leastPrimeAbove n)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p > leastPrimeAbove n)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p > leastPrimeAbove n)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p > leastPrimeAbove n)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p > leastPrimeAbove n)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p > leastPrimeAbove n)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hnp : n ≤ p) (hp : p.Prime), p ≥ leastPrimeAbove n

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n ≤ p) (hp : p.Prime), p ≥ leastPrimeAbove n) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n ≤ p) (hp : p.Prime), p ≥ leastPrimeAbove n) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n ≤ p) (hp : p.Prime), p ≥ leastPrimeAbove n) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n ≤ p) (hp : p.Prime), p ≥ leastPrimeAbove n) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n ≤ p) (hp : p.Prime), p ≥ leastPrimeAbove n) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n ≤ p) (hp : p.Prime), p ≥ leastPrimeAbove n) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n ≤ p) (hp : p.Prime), p ≥ leastPrimeAbove n) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (n < p) ↔ (n ≤ p) := by
  omega

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (n < p) ↔ (n ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (n < p) ↔ (n ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (n < p) ↔ (n ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (n < p) ↔ (n ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (n < p) ↔ (n ≤ p) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hp : p.Prime) :
    (n < p) ↔ (n ≤ p) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (p.Prime) ∧ (¬((n < p) ↔ (n ≤ p))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((n < p) ↔ (n ≤ p)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), p ≤ leastPrimeAbove n

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), p ≤ leastPrimeAbove n) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), p ≤ leastPrimeAbove n) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), p ≤ leastPrimeAbove n) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), p ≤ leastPrimeAbove n) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), p ≤ leastPrimeAbove n) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), p ≤ leastPrimeAbove n) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), p ≤ leastPrimeAbove n) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), p ≤ leastPrimeAbove n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), p ≤ leastPrimeAbove n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), p ≤ leastPrimeAbove n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), p ≤ leastPrimeAbove n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), p ≤ leastPrimeAbove n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), p ≤ leastPrimeAbove n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), leastPrimeAbove n ≤ p) →
    (∀ (n p : ℕ) (hnp : n < p) (hp : p.Prime), p ≤ leastPrimeAbove n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p ≤ leastPrimeAbove n)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p ≤ leastPrimeAbove n)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p ≤ leastPrimeAbove n)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p ≤ leastPrimeAbove n)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p ≤ leastPrimeAbove n)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p ≤ leastPrimeAbove n)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p ≤ leastPrimeAbove n)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p ≤ leastPrimeAbove n)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p ≤ leastPrimeAbove n)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p ≤ leastPrimeAbove n)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p ≤ leastPrimeAbove n)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p ≤ leastPrimeAbove n)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p ≤ leastPrimeAbove n)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p ≤ leastPrimeAbove n)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p ≤ leastPrimeAbove n)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p ≤ leastPrimeAbove n)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p ≤ leastPrimeAbove n)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p ≤ leastPrimeAbove n)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p ≤ leastPrimeAbove n)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p ≤ leastPrimeAbove n)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p ≤ leastPrimeAbove n)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p ≤ leastPrimeAbove n)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p ≤ leastPrimeAbove n)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p ≤ leastPrimeAbove n)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p ≤ leastPrimeAbove n)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p ≤ leastPrimeAbove n)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p ≤ leastPrimeAbove n)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p ≤ leastPrimeAbove n)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p ≤ leastPrimeAbove n)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p ≤ leastPrimeAbove n)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p ≤ leastPrimeAbove n)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), (n < p) ∧ (p.Prime) ∧ (¬(p ≤ leastPrimeAbove n)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p ≤ leastPrimeAbove n)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p ≤ leastPrimeAbove n)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p ≤ leastPrimeAbove n)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p ≤ leastPrimeAbove n)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p ≤ leastPrimeAbove n)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p ≤ leastPrimeAbove n)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p ≤ leastPrimeAbove n)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p ≤ leastPrimeAbove n)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p ≤ leastPrimeAbove n)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p ≤ leastPrimeAbove n)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p ≤ leastPrimeAbove n)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p ≤ leastPrimeAbove n)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p ≤ leastPrimeAbove n)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p ≤ leastPrimeAbove n)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p ≤ leastPrimeAbove n)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p ≤ leastPrimeAbove n)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p ≤ leastPrimeAbove n)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p ≤ leastPrimeAbove n)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p ≤ leastPrimeAbove n)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p ≤ leastPrimeAbove n)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p ≤ leastPrimeAbove n)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p ≤ leastPrimeAbove n)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p ≤ leastPrimeAbove n)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p ≤ leastPrimeAbove n)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p ≤ leastPrimeAbove n)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p ≤ leastPrimeAbove n)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p ≤ leastPrimeAbove n)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p ≤ leastPrimeAbove n)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p ≤ leastPrimeAbove n)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p ≤ leastPrimeAbove n)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p ≤ leastPrimeAbove n)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (p : ℕ), ¬((leastPrimeAbove n ≤ p) ↔ (p ≤ leastPrimeAbove n)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hnp : n < p) (hp : p.Prime) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hnp : n < p) (hp : p.Prime) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hnp : n < p) (hp : p.Prime) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hnp : n < p) (hp : p.Prime) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n p : ℕ) (hnp : n < p) (hp : p.Prime) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
