import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 709

*References:*
- [erdosproblems.com/709](https://www.erdosproblems.com/709)
- [ErSu59] P. Erdős and J. Surányi, Bemerkungen zu einer Aufgabe eines mathematischen
  Wettbewerbs, Mat. Lapok 10 (1959), 39–48.
- [Er92c] P. Erdős, Some of my forgotten problems in number theory, Hardy–Ramanujan J. 15
  (1992), 34–50.
- [vD26] W. van Doorn, On the length of an interval that contains distinct multiples of the
  first $n$ positive integers, Integers (2026), #A7.
-/

section

open Filter Asymptotics

namespace Erdos709

/-- The block of `length` consecutive positive integers immediately after `start`. -/
def window (start length : ℕ) : Finset ℕ := Finset.Icc (start + 1) (start + length)

/-- A block contains distinct multiples of all elements of `A`. -/
def HasDistinctMultiples (A : Finset ℕ) (start length : ℕ) : Prop :=
  ∃ choice : ℕ → ℕ,
    Set.InjOn choice (A : Set ℕ) ∧
    ∀ a ∈ A, choice a ∈ window start length ∧ a ∣ choice a

/-- The multiplier `k` works for all `n`-element inputs and all starting points.
`M` is required to be the largest element of `A`. -/
def Works (n k : ℕ) : Prop :=
  ∀ (A : Finset ℕ) (M : ℕ),
    A.card = n → M ∈ A → (∀ a ∈ A, a ≤ M) → (∀ a ∈ A, 2 ≤ a) →
    ∀ start : ℕ, HasDistinctMultiples A start (k * M)

/-- `k` is the least multiplier that works for inputs of size `n`. -/
def IsOptimal (n k : ℕ) : Prop := Works n k ∧ ∀ j < k, ¬ Works n j

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a M start : ℕ) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) →
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) →
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) →
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) →
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) →
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) →
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) →
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a M start : ℕ) (haM : a ≤ M) :
    (0 < a) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (a M start : ℕ) (haM : a ≤ M) :
    (0 < a) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a M start : ℕ) (haM : a ≤ M) :
    (0 < a) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a M start : ℕ) (haM : a ≤ M) :
    (0 < a) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a M start : ℕ) (haM : a ≤ M) :
    (0 < a) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a M start : ℕ) (haM : a ≤ M) :
    (0 < a) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a M start : ℕ) (haM : a ≤ M) :
    (0 < a) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((0 < a) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((0 < a) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((0 < a) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((0 < a) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((0 < a) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((0 < a) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a M start : ℕ) (ha : 0 < a) (haM : a < M), ∃ b ∈ window start M, a ∣ b

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) →
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a < M), ∃ b ∈ window start M, a ∣ b) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) →
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a < M), ∃ b ∈ window start M, a ∣ b) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) →
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a < M), ∃ b ∈ window start M, a ∣ b) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) →
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a < M), ∃ b ∈ window start M, a ∣ b) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) →
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a < M), ∃ b ∈ window start M, a ∣ b) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) →
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a < M), ∃ b ∈ window start M, a ∣ b) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) →
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a < M), ∃ b ∈ window start M, a ∣ b) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a M start : ℕ) (ha : 0 < a) :
    (a ≤ M) ↔ (a < M) := by
  omega

set_option maxHeartbeats 200000 in
example (a M start : ℕ) (ha : 0 < a) :
    (a ≤ M) ↔ (a < M) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a M start : ℕ) (ha : 0 < a) :
    (a ≤ M) ↔ (a < M) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a M start : ℕ) (ha : 0 < a) :
    (a ≤ M) ↔ (a < M) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a M start : ℕ) (ha : 0 < a) :
    (a ≤ M) ↔ (a < M) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a M start : ℕ) (ha : 0 < a) :
    (a ≤ M) ↔ (a < M) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a M start : ℕ) (ha : 0 < a) :
    (a ≤ M) ↔ (a < M) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a M start : ℕ) (ha : a > 0) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b

set_option maxHeartbeats 200000 in
example (a M start : ℕ) :
    (0 < a) ↔ (a > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (a M start : ℕ) :
    (0 < a) ↔ (a > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (a M start : ℕ) :
    (0 < a) ↔ (a > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (a M start : ℕ) :
    (0 < a) ↔ (a > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (a M start : ℕ) :
    (0 < a) ↔ (a > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (a M start : ℕ) :
    (0 < a) ↔ (a > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (a M start : ℕ) :
    (0 < a) ↔ (a > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (a M start : ℕ) :
    (0 < a) ↔ (a > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) ↔
    (∀ (a M start : ℕ) (ha : a > 0) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) ↔
    (∀ (a M start : ℕ) (ha : a > 0) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) ↔
    (∀ (a M start : ℕ) (ha : a > 0) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) ↔
    (∀ (a M start : ℕ) (ha : a > 0) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b₁ ∈ window start M, a ∣ b₁

set_option maxHeartbeats 200000 in
example (a M start : ℕ) :
    (∃ b ∈ window start M, a ∣ b) ↔ (∃ b₁ ∈ window start M, a ∣ b₁) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (a M start : ℕ) :
    (∃ b ∈ window start M, a ∣ b) ↔ (∃ b₁ ∈ window start M, a ∣ b₁) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (a M start : ℕ) :
    (∃ b ∈ window start M, a ∣ b) ↔ (∃ b₁ ∈ window start M, a ∣ b₁) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (a M start : ℕ) :
    (∃ b ∈ window start M, a ∣ b) ↔ (∃ b₁ ∈ window start M, a ∣ b₁) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (a M start : ℕ) :
    (∃ b ∈ window start M, a ∣ b) ↔ (∃ b₁ ∈ window start M, a ∣ b₁) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (a M start : ℕ) :
    (∃ b ∈ window start M, a ∣ b) ↔ (∃ b₁ ∈ window start M, a ∣ b₁) := by
  omega

set_option maxHeartbeats 200000 in
example (a M start : ℕ) :
    (∃ b ∈ window start M, a ∣ b) ↔ (∃ b₁ ∈ window start M, a ∣ b₁) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (a M start : ℕ) :
    (∃ b ∈ window start M, a ∣ b) ↔ (∃ b₁ ∈ window start M, a ∣ b₁) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) ↔
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b₁ ∈ window start M, a ∣ b₁) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) ↔
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b₁ ∈ window start M, a ∣ b₁) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) ↔
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b₁ ∈ window start M, a ∣ b₁) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) ↔
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b₁ ∈ window start M, a ∣ b₁) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a M start : ℕ) (haM : a ≤ M) (ha : 0 < a), ∃ b ∈ window start M, a ∣ b

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) ↔
    (∀ (a M start : ℕ) (haM : a ≤ M) (ha : 0 < a), ∃ b ∈ window start M, a ∣ b) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) ↔
    (∀ (a M start : ℕ) (haM : a ≤ M) (ha : 0 < a), ∃ b ∈ window start M, a ∣ b) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) ↔
    (∀ (a M start : ℕ) (haM : a ≤ M) (ha : 0 < a), ∃ b ∈ window start M, a ∣ b) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) ↔
    (∀ (a M start : ℕ) (haM : a ≤ M) (ha : 0 < a), ∃ b ∈ window start M, a ∣ b) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a M start : ℕ) (ha₀ : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) ↔
    (∀ (a M start : ℕ) (ha₀ : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) ↔
    (∀ (a M start : ℕ) (ha₀ : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) ↔
    (∀ (a M start : ℕ) (ha₀ : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) ↔
    (∀ (a M start : ℕ) (ha₀ : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a M start : ℕ) (ha : ¬(a ≤ 0)) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b

set_option maxHeartbeats 200000 in
example (a M start : ℕ) :
    (0 < a) ↔ (¬(a ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (a M start : ℕ) :
    (0 < a) ↔ (¬(a ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (a M start : ℕ) :
    (0 < a) ↔ (¬(a ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (a M start : ℕ) :
    (0 < a) ↔ (¬(a ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (a M start : ℕ) :
    (0 < a) ↔ (¬(a ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (a M start : ℕ) :
    (0 < a) ↔ (¬(a ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (a M start : ℕ) :
    (0 < a) ↔ (¬(a ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (a M start : ℕ) :
    (0 < a) ↔ (¬(a ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) ↔
    (∀ (a M start : ℕ) (ha : ¬(a ≤ 0)) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) ↔
    (∀ (a M start : ℕ) (ha : ¬(a ≤ 0)) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) ↔
    (∀ (a M start : ℕ) (ha : ¬(a ≤ 0)) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) ↔
    (∀ (a M start : ℕ) (ha : ¬(a ≤ 0)) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a M start : ℕ) (ha : 1 ≤ a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b

set_option maxHeartbeats 200000 in
example (a M start : ℕ) :
    (0 < a) ↔ (1 ≤ a) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (a M start : ℕ) :
    (0 < a) ↔ (1 ≤ a) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (a M start : ℕ) :
    (0 < a) ↔ (1 ≤ a) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (a M start : ℕ) :
    (0 < a) ↔ (1 ≤ a) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (a M start : ℕ) :
    (0 < a) ↔ (1 ≤ a) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (a M start : ℕ) :
    (0 < a) ↔ (1 ≤ a) := by
  omega

set_option maxHeartbeats 200000 in
example (a M start : ℕ) :
    (0 < a) ↔ (1 ≤ a) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (a M start : ℕ) :
    (0 < a) ↔ (1 ≤ a) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) ↔
    (∀ (a M start : ℕ) (ha : 1 ≤ a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) ↔
    (∀ (a M start : ℕ) (ha : 1 ≤ a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) ↔
    (∀ (a M start : ℕ) (ha : 1 ≤ a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) ↔
    (∀ (a M start : ℕ) (ha : 1 ≤ a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a M start : ℕ) (ha : a > 0) (haM : a < M), ∃ b ∈ window start M, a ∣ b

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) →
    (∀ (a M start : ℕ) (ha : a > 0) (haM : a < M), ∃ b ∈ window start M, a ∣ b) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) →
    (∀ (a M start : ℕ) (ha : a > 0) (haM : a < M), ∃ b ∈ window start M, a ∣ b) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) →
    (∀ (a M start : ℕ) (ha : a > 0) (haM : a < M), ∃ b ∈ window start M, a ∣ b) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) →
    (∀ (a M start : ℕ) (ha : a > 0) (haM : a < M), ∃ b ∈ window start M, a ∣ b) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) →
    (∀ (a M start : ℕ) (ha : a > 0) (haM : a < M), ∃ b ∈ window start M, a ∣ b) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) →
    (∀ (a M start : ℕ) (ha : a > 0) (haM : a < M), ∃ b ∈ window start M, a ∣ b) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) →
    (∀ (a M start : ℕ) (ha : a > 0) (haM : a < M), ∃ b ∈ window start M, a ∣ b) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a M start : ℕ) (ha : 0 < a) :
    (a ≤ M) ↔ (a < M) := by
  omega

set_option maxHeartbeats 200000 in
example (a M start : ℕ) (ha : 0 < a) :
    (a ≤ M) ↔ (a < M) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a M start : ℕ) (ha : 0 < a) :
    (a ≤ M) ↔ (a < M) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a M start : ℕ) (ha : 0 < a) :
    (a ≤ M) ↔ (a < M) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a M start : ℕ) (ha : 0 < a) :
    (a ≤ M) ↔ (a < M) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a M start : ℕ) (ha : 0 < a) :
    (a ≤ M) ↔ (a < M) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a M start : ℕ) (ha : 0 < a) :
    (a ≤ M) ↔ (a < M) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (a < M))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (a < M)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a M start : ℕ) (ha : 1 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) →
    (∀ (a M start : ℕ) (ha : 1 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) →
    (∀ (a M start : ℕ) (ha : 1 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) →
    (∀ (a M start : ℕ) (ha : 1 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) →
    (∀ (a M start : ℕ) (ha : 1 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) →
    (∀ (a M start : ℕ) (ha : 1 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) →
    (∀ (a M start : ℕ) (ha : 1 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) →
    (∀ (a M start : ℕ) (ha : 1 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a M start : ℕ) (haM : a ≤ M) :
    (0 < a) ↔ (1 < a) := by
  omega

set_option maxHeartbeats 200000 in
example (a M start : ℕ) (haM : a ≤ M) :
    (0 < a) ↔ (1 < a) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a M start : ℕ) (haM : a ≤ M) :
    (0 < a) ↔ (1 < a) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a M start : ℕ) (haM : a ≤ M) :
    (0 < a) ↔ (1 < a) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a M start : ℕ) (haM : a ≤ M) :
    (0 < a) ↔ (1 < a) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a M start : ℕ) (haM : a ≤ M) :
    (0 < a) ↔ (1 < a) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a M start : ℕ) (haM : a ≤ M) :
    (0 < a) ↔ (1 < a) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (a ≤ M) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((0 < a) ↔ (1 < a)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((0 < a) ↔ (1 < a)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((0 < a) ↔ (1 < a)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((0 < a) ↔ (1 < a)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((0 < a) ↔ (1 < a)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((0 < a) ↔ (1 < a)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a M start : ℕ) (ha : 0 < a), ∃ b ∈ window start M, a ∣ b

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a), ∃ b ∈ window start M, a ∣ b) →
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a), ∃ b ∈ window start M, a ∣ b) →
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a), ∃ b ∈ window start M, a ∣ b) →
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a), ∃ b ∈ window start M, a ∣ b) →
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a), ∃ b ∈ window start M, a ∣ b) →
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a), ∃ b ∈ window start M, a ∣ b) →
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a M start : ℕ) (ha : 0 < a), ∃ b ∈ window start M, a ∣ b) →
    (∀ (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M), ∃ b ∈ window start M, a ∣ b) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a M start : ℕ) (ha : 0 < a) :
    (a ≤ M) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (a M start : ℕ) (ha : 0 < a) :
    (a ≤ M) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a M start : ℕ) (ha : 0 < a) :
    (a ≤ M) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a M start : ℕ) (ha : 0 < a) :
    (a ≤ M) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a M start : ℕ) (ha : 0 < a) :
    (a ≤ M) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a M start : ℕ) (ha : 0 < a) :
    (a ≤ M) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a M start : ℕ) (ha : 0 < a) :
    (a ≤ M) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (True))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (True))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (True))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (True))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (True))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (True))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (True))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (True))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (True))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (True))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (True))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (True))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (True))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (True))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (True))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (True))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (True))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (True))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), (0 < a) ∧ (¬((a ≤ M) ↔ (True))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (True)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (True)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (True)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (True)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (True)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (True)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (True)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (True)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (True)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (True)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (True)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (True)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (True)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (True)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (True)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (True)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (True)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (True)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (True)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (True)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (True)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (True)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (True)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (True)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (True)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (True)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (True)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (True)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (True)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (True)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (True)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (M : ℕ), ¬((a ≤ M) ↔ (True)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (a M start : ℕ) (ha : 0 < a) (haM : a ≤ M) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
