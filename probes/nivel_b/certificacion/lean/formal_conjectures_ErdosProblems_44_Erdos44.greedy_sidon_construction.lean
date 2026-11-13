import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Combinatorics.Basic
/-!
# Erdős Problem 44: Extending Sidon Sets

*References:*
- [erdosproblems.com/44](https://www.erdosproblems.com/44)
- [Si38] Singer, James, A theorem in finite projective geometry and some applications to number
  theory. Trans. Amer. Math. Soc. (1938), 377--385.
-/

section

open Function Set Finset

namespace Erdos44

-- Reference: https://arxiv.org/pdf/2103.15850

/-  ## Related results and examples -/

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔ (∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔ (∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔ (∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔ (∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔ (∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔ (∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔ (∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (hN : 1 < N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 < N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 < N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 < N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 < N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 < N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 < N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 < N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (1 ≤ N) ↔ (1 < N) := by
  omega

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (1 ≤ N) ↔ (1 < N) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (1 ≤ N) ↔ (1 < N) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (1 ≤ N) ↔ (1 < N) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (1 ≤ N) ↔ (1 < N) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (1 ≤ N) ↔ (1 < N) := by
  simp_all

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (1 ≤ N) ↔ (1 < N) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((1 ≤ N) ↔ (1 < N))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((1 ≤ N) ↔ (1 < N))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((1 ≤ N) ↔ (1 < N))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((1 ≤ N) ↔ (1 < N))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((1 ≤ N) ↔ (1 < N))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((1 ≤ N) ↔ (1 < N))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ N) ↔ (1 < N)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ N) ↔ (1 < N)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ N) ↔ (1 < N)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ N) ↔ (1 < N)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ N) ↔ (1 < N)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ N) ↔ (1 < N)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔ (∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔ (∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔ (∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔ (∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔ (∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔ (∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔ (∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (hN : N ≥ 1), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (1 ≤ N) ↔ (N ≥ 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (1 ≤ N) ↔ (N ≥ 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (1 ≤ N) ↔ (N ≥ 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (1 ≤ N) ↔ (N ≥ 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (1 ≤ N) ↔ (N ≥ 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (1 ≤ N) ↔ (N ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (1 ≤ N) ↔ (N ≥ 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (1 ≤ N) ↔ (N ≥ 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔
    (∀ (N : ℕ) (hN : N ≥ 1), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔
    (∀ (N : ℕ) (hN : N ≥ 1), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔
    (∀ (N : ℕ) (hN : N ≥ 1), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔
    (∀ (N : ℕ) (hN : N ≥ 1), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (hN₀ : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔
    (∀ (N : ℕ) (hN₀ : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔
    (∀ (N : ℕ) (hN₀ : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔
    (∀ (N : ℕ) (hN₀ : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔
    (∀ (N : ℕ) (hN₀ : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (hN : ¬(N < 1)), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (1 ≤ N) ↔ (¬(N < 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (1 ≤ N) ↔ (¬(N < 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (1 ≤ N) ↔ (¬(N < 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (1 ≤ N) ↔ (¬(N < 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (1 ≤ N) ↔ (¬(N < 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (1 ≤ N) ↔ (¬(N < 1)) := by
  omega

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (1 ≤ N) ↔ (¬(N < 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (1 ≤ N) ↔ (¬(N < 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔
    (∀ (N : ℕ) (hN : ¬(N < 1)), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔
    (∀ (N : ℕ) (hN : ¬(N < 1)), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔
    (∀ (N : ℕ) (hN : ¬(N < 1)), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔
    (∀ (N : ℕ) (hN : ¬(N < 1)), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (hN : 0 < N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (1 ≤ N) ↔ (0 < N) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (1 ≤ N) ↔ (0 < N) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (1 ≤ N) ↔ (0 < N) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (1 ≤ N) ↔ (0 < N) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (1 ≤ N) ↔ (0 < N) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (1 ≤ N) ↔ (0 < N) := by
  omega

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (1 ≤ N) ↔ (0 < N) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (N : ℕ) :
    (1 ≤ N) ↔ (0 < N) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔
    (∀ (N : ℕ) (hN : 0 < N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔
    (∀ (N : ℕ) (hN : 0 < N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔
    (∀ (N : ℕ) (hN : 0 < N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔
    (∀ (N : ℕ) (hN : 0 < N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (hN : N ≥ 1), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : N ≥ 1), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : N ≥ 1), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : N ≥ 1), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : N ≥ 1), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : N ≥ 1), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : N ≥ 1), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : N ≥ 1), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔ (∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔ (∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔ (∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔ (∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔ (∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔ (∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔ (∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (hN : N > 1), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) →
    (∀ (N : ℕ) (hN : N > 1), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) →
    (∀ (N : ℕ) (hN : N > 1), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) →
    (∀ (N : ℕ) (hN : N > 1), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) →
    (∀ (N : ℕ) (hN : N > 1), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) →
    (∀ (N : ℕ) (hN : N > 1), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) →
    (∀ (N : ℕ) (hN : N > 1), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) →
    (∀ (N : ℕ) (hN : N > 1), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (1 ≤ N) ↔ (N > 1) := by
  omega

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (1 ≤ N) ↔ (N > 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (1 ≤ N) ↔ (N > 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (1 ≤ N) ↔ (N > 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (1 ≤ N) ↔ (N > 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (1 ≤ N) ↔ (N > 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example (N : ℕ)  :
    (1 ≤ N) ↔ (N > 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((1 ≤ N) ↔ (N > 1))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((1 ≤ N) ↔ (N > 1))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((1 ≤ N) ↔ (N > 1))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((1 ≤ N) ↔ (N > 1))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((1 ≤ N) ↔ (N > 1))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (¬((1 ≤ N) ↔ (N > 1))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ N) ↔ (N > 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ N) ↔ (N > 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ N) ↔ (N > 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ N) ↔ (N > 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ N) ↔ (N > 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((1 ≤ N) ↔ (N > 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (hN : N ≥ 1), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : N ≥ 1), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : N ≥ 1), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : N ≥ 1), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : N ≥ 1), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : N ≥ 1), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : N ≥ 1), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : N ≥ 1), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) →
    (∀ (N : ℕ) (hN : N ≥ 1), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) →
    (∀ (N : ℕ) (hN : N ≥ 1), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) →
    (∀ (N : ℕ) (hN : N ≥ 1), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) →
    (∀ (N : ℕ) (hN : N ≥ 1), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) →
    (∀ (N : ℕ) (hN : N ≥ 1), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) →
    (∀ (N : ℕ) (hN : N ≥ 1), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) →
    (∀ (N : ℕ) (hN : N ≥ 1), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔ (∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔ (∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔ (∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔ (∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔ (∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔ (∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔ (∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (hN : 0 < N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 0 < N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 0 < N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 0 < N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 0 < N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 0 < N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 0 < N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 0 < N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔ (∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔ (∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔ (∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔ (∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔ (∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔ (∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔ (∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N < A.card ^ 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (N : ℕ) (hN : 0 < N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 0 < N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 0 < N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 0 < N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 0 < N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 0 < N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 0 < N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 0 < N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3) →
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) →
    (∀ (N : ℕ) (hN : 0 < N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) →
    (∀ (N : ℕ) (hN : 0 < N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) →
    (∀ (N : ℕ) (hN : 0 < N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) →
    (∀ (N : ℕ) (hN : 0 < N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) →
    (∀ (N : ℕ) (hN : 0 < N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) →
    (∀ (N : ℕ) (hN : 0 < N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (N : ℕ) (hN : 1 ≤ N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) →
    (∀ (N : ℕ) (hN : 0 < N), ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), (1 ≤ N) ∧ (¬(∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔ (∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔ (∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔ (∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔ (∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔ (∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔ (∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (N : ℕ), ¬((∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3) ↔ (∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≥ A.card ^ 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (N : ℕ) (hN : 1 ≤ N) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (N : ℕ) (hN : 1 ≤ N) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (N : ℕ) (hN : 1 ≤ N) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (N : ℕ) (hN : 1 ≤ N) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (N : ℕ) (hN : 1 ≤ N) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
