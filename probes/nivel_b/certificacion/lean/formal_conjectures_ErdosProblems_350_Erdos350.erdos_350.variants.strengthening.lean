import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 350

*References:*
- [erdosproblems.com/350](https://www.erdosproblems.com/350)
- [BeEr74] Benkoski, S. J. and Erdős, P., On weird and pseudoperfect numbers. Math. Comp. (1974),
  617-623.
- [HSS77] Hanson, F. and Steele, J. M. and Stenger, F., Distinct sums over subsets. Proc. Amer.
  Math. Soc. (1977), 179-180.
-/

section

namespace Erdos350

/-- The predicate that all (finite) subsets of `A` have distinct sums. -/
def DistinctSubsetSums {M : Type*} [AddCommMonoid M] (A : Set M) : Prop :=
  Set.Pairwise {X : Finset M | ↑X ⊆ A} fun X Y => X.sum id ≠ Y.sum id

/-- The predicate that all (finite) subsets of `A` have distinct sums, decidable version -/
def DecidableDistinctSubsetSums {M : Type*} [AddCommMonoid M] [DecidableEq M] (A : Finset M) : Prop :=
  ∀ X ⊆ A, ∀ Y ⊆ A, X ≠ Y → X.sum id ≠ Y.sum id

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (s : ℝ) (hA : DecidableDistinctSubsetSums A) :
    (0 < s) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (s : ℝ) (hA : DecidableDistinctSubsetSums A) :
    (0 < s) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (s : ℝ) (hA : DecidableDistinctSubsetSums A) :
    (0 < s) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (s : ℝ) (hA : DecidableDistinctSubsetSums A) :
    (0 < s) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (s : ℝ) (hA : DecidableDistinctSubsetSums A) :
    (0 < s) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (s : ℝ) (hA : DecidableDistinctSubsetSums A) :
    (0 < s) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (s : ℝ) (hA : DecidableDistinctSubsetSums A) :
    (0 < s) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (s : ℝ), ¬((0 < s) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (s : ℝ), ¬((0 < s) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (s : ℝ), ¬((0 < s) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (s : ℝ), ¬((0 < s) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (s : ℝ), ¬((0 < s) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (s : ℝ), ¬((0 < s) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 ≤ s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 ≤ s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 ≤ s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 ≤ s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 ≤ s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 ≤ s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 ≤ s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 ≤ s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (s : ℝ) (hA : DecidableDistinctSubsetSums A) :
    (0 < s) ↔ (0 ≤ s) := by
  omega

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (s : ℝ) (hA : DecidableDistinctSubsetSums A) :
    (0 < s) ↔ (0 ≤ s) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (s : ℝ) (hA : DecidableDistinctSubsetSums A) :
    (0 < s) ↔ (0 ≤ s) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (s : ℝ) (hA : DecidableDistinctSubsetSums A) :
    (0 < s) ↔ (0 ≤ s) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (s : ℝ) (hA : DecidableDistinctSubsetSums A) :
    (0 < s) ↔ (0 ≤ s) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (s : ℝ) (hA : DecidableDistinctSubsetSums A) :
    (0 < s) ↔ (0 ≤ s) := by
  simp_all

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (s : ℝ) (hA : DecidableDistinctSubsetSums A) :
    (0 < s) ↔ (0 ≤ s) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (s : ℝ), ¬((0 < s) ↔ (0 ≤ s)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (s : ℝ), ¬((0 < s) ↔ (0 ≤ s)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (s : ℝ), ¬((0 < s) ↔ (0 ≤ s)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (s : ℝ), ¬((0 < s) ↔ (0 ≤ s)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (s : ℝ), ¬((0 < s) ↔ (0 ≤ s)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (s : ℝ), ¬((0 < s) ↔ (0 ≤ s)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s ≤ 1 / (1 - 2^(-s))

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s ≤ 1 / (1 - 2^(-s))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s ≤ 1 / (1 - 2^(-s))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s ≤ 1 / (1 - 2^(-s))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s ≤ 1 / (1 - 2^(-s))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s ≤ 1 / (1 - 2^(-s))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s ≤ 1 / (1 - 2^(-s))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s ≤ 1 / (1 - 2^(-s))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 3^(-s))

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 3^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 3^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 3^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 3^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 3^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 3^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 3^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 3^(-s))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 3^(-s))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 3^(-s))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 3^(-s))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 3^(-s))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 3^(-s))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 3^(-s))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s > 1 / (1 - 2^(-s))

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s > 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s > 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s > 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s > 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s > 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s > 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s > 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s > 1 / (1 - 2^(-s))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s > 1 / (1 - 2^(-s))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s > 1 / (1 - 2^(-s))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s > 1 / (1 - 2^(-s))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s > 1 / (1 - 2^(-s))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s > 1 / (1 - 2^(-s))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s > 1 / (1 - 2^(-s))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s > 0), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (s : ℝ) :
    (0 < s) ↔ (s > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (s : ℝ) :
    (0 < s) ↔ (s > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (s : ℝ) :
    (0 < s) ↔ (s > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (s : ℝ) :
    (0 < s) ↔ (s > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (s : ℝ) :
    (0 < s) ↔ (s > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (s : ℝ) :
    (0 < s) ↔ (s > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (s : ℝ) :
    (0 < s) ↔ (s > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (s : ℝ) :
    (0 < s) ↔ (s > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) ↔
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s > 0), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) ↔
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s > 0), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) ↔
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s > 0), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) ↔
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s > 0), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ) (hA₀ : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) ↔
    (∀ (A : Finset ℕ) (hA₀ : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) ↔
    (∀ (A : Finset ℕ) (hA₀ : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) ↔
    (∀ (A : Finset ℕ) (hA₀ : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) ↔
    (∀ (A : Finset ℕ) (hA₀ : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : ¬(s ≤ 0)), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (s : ℝ) :
    (0 < s) ↔ (¬(s ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (s : ℝ) :
    (0 < s) ↔ (¬(s ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (s : ℝ) :
    (0 < s) ↔ (¬(s ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (s : ℝ) :
    (0 < s) ↔ (¬(s ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (s : ℝ) :
    (0 < s) ↔ (¬(s ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (s : ℝ) :
    (0 < s) ↔ (¬(s ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (s : ℝ) :
    (0 < s) ↔ (¬(s ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (s : ℝ) :
    (0 < s) ↔ (¬(s ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) ↔
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : ¬(s ≤ 0)), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) ↔
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : ¬(s ≤ 0)), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) ↔
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : ¬(s ≤ 0)), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) ↔
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : ¬(s ≤ 0)), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s ≥ 0), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s ≥ 0), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s ≥ 0), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s ≥ 0), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s ≥ 0), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s ≥ 0), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s ≥ 0), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s ≥ 0), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (s : ℝ) (hA : DecidableDistinctSubsetSums A) :
    (0 < s) ↔ (s ≥ 0) := by
  omega

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (s : ℝ) (hA : DecidableDistinctSubsetSums A) :
    (0 < s) ↔ (s ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (s : ℝ) (hA : DecidableDistinctSubsetSums A) :
    (0 < s) ↔ (s ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (s : ℝ) (hA : DecidableDistinctSubsetSums A) :
    (0 < s) ↔ (s ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (s : ℝ) (hA : DecidableDistinctSubsetSums A) :
    (0 < s) ↔ (s ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (s : ℝ) (hA : DecidableDistinctSubsetSums A) :
    (0 < s) ↔ (s ≥ 0) := by
  simp_all

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (s : ℝ) (hA : DecidableDistinctSubsetSums A) :
    (0 < s) ↔ (s ≥ 0) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (s : ℝ), ¬((0 < s) ↔ (s ≥ 0)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (s : ℝ), ¬((0 < s) ↔ (s ≥ 0)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (s : ℝ), ¬((0 < s) ↔ (s ≥ 0)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (s : ℝ), ¬((0 < s) ↔ (s ≥ 0)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (s : ℝ), ¬((0 < s) ↔ (s ≥ 0)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (s : ℝ), ¬((0 < s) ↔ (s ≥ 0)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s > 0), ∑ n ∈ A, (1 / n : ℝ)^s ≤ 1 / (1 - 2^(-s))

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s > 0), ∑ n ∈ A, (1 / n : ℝ)^s ≤ 1 / (1 - 2^(-s))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s > 0), ∑ n ∈ A, (1 / n : ℝ)^s ≤ 1 / (1 - 2^(-s))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s > 0), ∑ n ∈ A, (1 / n : ℝ)^s ≤ 1 / (1 - 2^(-s))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s > 0), ∑ n ∈ A, (1 / n : ℝ)^s ≤ 1 / (1 - 2^(-s))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s > 0), ∑ n ∈ A, (1 / n : ℝ)^s ≤ 1 / (1 - 2^(-s))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s > 0), ∑ n ∈ A, (1 / n : ℝ)^s ≤ 1 / (1 - 2^(-s))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s > 0), ∑ n ∈ A, (1 / n : ℝ)^s ≤ 1 / (1 - 2^(-s))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s > 0), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 3^(-s))

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s > 0), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 3^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s > 0), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 3^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s > 0), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 3^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s > 0), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 3^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s > 0), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 3^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s > 0), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 3^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s > 0), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 3^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s > 0), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 3^(-s))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s > 0), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 3^(-s))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s > 0), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 3^(-s))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s > 0), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 3^(-s))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s > 0), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 3^(-s))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s > 0), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 3^(-s))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s > 0), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 3^(-s))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s > 0), ∑ n ∈ A, (1 / n : ℝ)^s > 1 / (1 - 2^(-s))

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s > 0), ∑ n ∈ A, (1 / n : ℝ)^s > 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s > 0), ∑ n ∈ A, (1 / n : ℝ)^s > 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s > 0), ∑ n ∈ A, (1 / n : ℝ)^s > 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s > 0), ∑ n ∈ A, (1 / n : ℝ)^s > 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s > 0), ∑ n ∈ A, (1 / n : ℝ)^s > 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s > 0), ∑ n ∈ A, (1 / n : ℝ)^s > 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s > 0), ∑ n ∈ A, (1 / n : ℝ)^s > 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s > 0), ∑ n ∈ A, (1 / n : ℝ)^s > 1 / (1 - 2^(-s))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s > 0), ∑ n ∈ A, (1 / n : ℝ)^s > 1 / (1 - 2^(-s))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s > 0), ∑ n ∈ A, (1 / n : ℝ)^s > 1 / (1 - 2^(-s))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s > 0), ∑ n ∈ A, (1 / n : ℝ)^s > 1 / (1 - 2^(-s))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s > 0), ∑ n ∈ A, (1 / n : ℝ)^s > 1 / (1 - 2^(-s))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s > 0), ∑ n ∈ A, (1 / n : ℝ)^s > 1 / (1 - 2^(-s))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : 0 < s), ∑ n ∈ A, (1 / n : ℝ)^s < 1 / (1 - 2^(-s))) →
    (∀ (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) (s : ℝ) (hs : s > 0), ∑ n ∈ A, (1 / n : ℝ)^s > 1 / (1 - 2^(-s))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (s : ℝ) (hA : DecidableDistinctSubsetSums A) (hs : 0 < s) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (s : ℝ) (hA : DecidableDistinctSubsetSums A) (hs : 0 < s) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (s : ℝ) (hA : DecidableDistinctSubsetSums A) (hs : 0 < s) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (s : ℝ) (hA : DecidableDistinctSubsetSums A) (hs : 0 < s) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (A : Finset ℕ) (s : ℝ) (hA : DecidableDistinctSubsetSums A) (hs : 0 < s) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
