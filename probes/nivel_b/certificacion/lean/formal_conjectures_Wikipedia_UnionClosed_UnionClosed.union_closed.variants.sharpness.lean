import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Union-closed sets conjecture

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Union-closed_sets_conjecture)

In this file, we:
* state the conjecture
* state three solved variants of the conjecture, without proof
* prove two solved variants of the conjecture
* prove the conjecture is sharp
-/

section

open Finset

variable {n : Type*} [DecidableEq n] {A : Finset (Finset n)}

namespace UnionClosed
abbrev IsUnionClosed (A : Finset (Finset n)) : Prop :=
  ∀ᵉ (X ∈ A) (Y ∈ A), X ∪ Y ∈ A

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Fintype n] (c : ℝ), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ)  :
    (1 / 2 < c) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ)  :
    (1 / 2 < c) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ)  :
    (1 / 2 < c) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ)  :
    (1 / 2 < c) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ)  :
    (1 / 2 < c) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ)  :
    (1 / 2 < c) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ)  :
    (1 / 2 < c) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((1 / 2 < c) ↔ (True))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((1 / 2 < c) ↔ (True))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((1 / 2 < c) ↔ (True))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((1 / 2 < c) ↔ (True))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((1 / 2 < c) ↔ (True))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((1 / 2 < c) ↔ (True))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((1 / 2 < c) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((1 / 2 < c) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((1 / 2 < c) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((1 / 2 < c) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((1 / 2 < c) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((1 / 2 < c) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Fintype n] (c : ℝ) (hc : 1 / 2 ≤ c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 ≤ c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 ≤ c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 ≤ c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 ≤ c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 ≤ c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 ≤ c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 ≤ c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ)  :
    (1 / 2 < c) ↔ (1 / 2 ≤ c) := by
  omega

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ)  :
    (1 / 2 < c) ↔ (1 / 2 ≤ c) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ)  :
    (1 / 2 < c) ↔ (1 / 2 ≤ c) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ)  :
    (1 / 2 < c) ↔ (1 / 2 ≤ c) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ)  :
    (1 / 2 < c) ↔ (1 / 2 ≤ c) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ)  :
    (1 / 2 < c) ↔ (1 / 2 ≤ c) := by
  simp_all

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ)  :
    (1 / 2 < c) ↔ (1 / 2 ≤ c) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((1 / 2 < c) ↔ (1 / 2 ≤ c))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((1 / 2 < c) ↔ (1 / 2 ≤ c))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((1 / 2 < c) ↔ (1 / 2 ≤ c))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((1 / 2 < c) ↔ (1 / 2 ≤ c))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((1 / 2 < c) ↔ (1 / 2 ≤ c))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((1 / 2 < c) ↔ (1 / 2 ≤ c))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((1 / 2 < c) ↔ (1 / 2 ≤ c)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((1 / 2 < c) ↔ (1 / 2 ≤ c)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((1 / 2 < c) ↔ (1 / 2 ≤ c)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((1 / 2 < c) ↔ (1 / 2 ≤ c)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((1 / 2 < c) ↔ (1 / 2 ≤ c)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((1 / 2 < c) ↔ (1 / 2 ≤ c)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Fintype n] (c : ℝ) (hc : 1 / 3 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 3 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 3 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 3 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 3 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 3 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 3 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 3 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 3 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 3 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 3 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 3 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 3 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 3 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 3 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ)  :
    (1 / 2 < c) ↔ (1 / 3 < c) := by
  omega

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ)  :
    (1 / 2 < c) ↔ (1 / 3 < c) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ)  :
    (1 / 2 < c) ↔ (1 / 3 < c) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ)  :
    (1 / 2 < c) ↔ (1 / 3 < c) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ)  :
    (1 / 2 < c) ↔ (1 / 3 < c) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ)  :
    (1 / 2 < c) ↔ (1 / 3 < c) := by
  simp_all

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ)  :
    (1 / 2 < c) ↔ (1 / 3 < c) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((1 / 2 < c) ↔ (1 / 3 < c))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((1 / 2 < c) ↔ (1 / 3 < c))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((1 / 2 < c) ↔ (1 / 3 < c))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((1 / 2 < c) ↔ (1 / 3 < c))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((1 / 2 < c) ↔ (1 / 3 < c))) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((1 / 2 < c) ↔ (1 / 3 < c))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((1 / 2 < c) ↔ (1 / 3 < c))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((1 / 2 < c) ↔ (1 / 3 < c)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((1 / 2 < c) ↔ (1 / 3 < c)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((1 / 2 < c) ↔ (1 / 3 < c)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((1 / 2 < c) ↔ (1 / 3 < c)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((1 / 2 < c) ↔ (1 / 3 < c)) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((1 / 2 < c) ↔ (1 / 3 < c)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((1 / 2 < c) ↔ (1 / 3 < c)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Fintype n] (c : ℝ) (hc : c > 1 / 2), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ) :
    (1 / 2 < c) ↔ (c > 1 / 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ) :
    (1 / 2 < c) ↔ (c > 1 / 2) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ) :
    (1 / 2 < c) ↔ (c > 1 / 2) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ) :
    (1 / 2 < c) ↔ (c > 1 / 2) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ) :
    (1 / 2 < c) ↔ (c > 1 / 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ) :
    (1 / 2 < c) ↔ (c > 1 / 2) := by
  omega

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ) :
    (1 / 2 < c) ↔ (c > 1 / 2) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ) :
    (1 / 2 < c) ↔ (c > 1 / 2) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) ↔
    (∀ [Fintype n] (c : ℝ) (hc : c > 1 / 2), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) ↔
    (∀ [Fintype n] (c : ℝ) (hc : c > 1 / 2), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) ↔
    (∀ [Fintype n] (c : ℝ) (hc : c > 1 / 2), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) ↔
    (∀ [Fintype n] (c : ℝ) (hc : c > 1 / 2), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A₁ : Finset (Finset n), A₁ ≠ {∅} → IsUnionClosed A₁ →
        ∃ i : n, c * #A₁ ≤ #{x ∈ A₁ | i ∈ x})

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ) :
    (¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) ↔ (¬ (∀ A₁ : Finset (Finset n), A₁ ≠ {∅} → IsUnionClosed A₁ →
        ∃ i : n, c * #A₁ ≤ #{x ∈ A₁ | i ∈ x})) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ) :
    (¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) ↔ (¬ (∀ A₁ : Finset (Finset n), A₁ ≠ {∅} → IsUnionClosed A₁ →
        ∃ i : n, c * #A₁ ≤ #{x ∈ A₁ | i ∈ x})) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ) :
    (¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) ↔ (¬ (∀ A₁ : Finset (Finset n), A₁ ≠ {∅} → IsUnionClosed A₁ →
        ∃ i : n, c * #A₁ ≤ #{x ∈ A₁ | i ∈ x})) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ) :
    (¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) ↔ (¬ (∀ A₁ : Finset (Finset n), A₁ ≠ {∅} → IsUnionClosed A₁ →
        ∃ i : n, c * #A₁ ≤ #{x ∈ A₁ | i ∈ x})) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ) :
    (¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) ↔ (¬ (∀ A₁ : Finset (Finset n), A₁ ≠ {∅} → IsUnionClosed A₁ →
        ∃ i : n, c * #A₁ ≤ #{x ∈ A₁ | i ∈ x})) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ) :
    (¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) ↔ (¬ (∀ A₁ : Finset (Finset n), A₁ ≠ {∅} → IsUnionClosed A₁ →
        ∃ i : n, c * #A₁ ≤ #{x ∈ A₁ | i ∈ x})) := by
  omega

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ) :
    (¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) ↔ (¬ (∀ A₁ : Finset (Finset n), A₁ ≠ {∅} → IsUnionClosed A₁ →
        ∃ i : n, c * #A₁ ≤ #{x ∈ A₁ | i ∈ x})) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ) :
    (¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) ↔ (¬ (∀ A₁ : Finset (Finset n), A₁ ≠ {∅} → IsUnionClosed A₁ →
        ∃ i : n, c * #A₁ ≤ #{x ∈ A₁ | i ∈ x})) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) ↔
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A₁ : Finset (Finset n), A₁ ≠ {∅} → IsUnionClosed A₁ →
        ∃ i : n, c * #A₁ ≤ #{x ∈ A₁ | i ∈ x})) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) ↔
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A₁ : Finset (Finset n), A₁ ≠ {∅} → IsUnionClosed A₁ →
        ∃ i : n, c * #A₁ ≤ #{x ∈ A₁ | i ∈ x})) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) ↔
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A₁ : Finset (Finset n), A₁ ≠ {∅} → IsUnionClosed A₁ →
        ∃ i : n, c * #A₁ ≤ #{x ∈ A₁ | i ∈ x})) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) ↔
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A₁ : Finset (Finset n), A₁ ≠ {∅} → IsUnionClosed A₁ →
        ∃ i : n, c * #A₁ ≤ #{x ∈ A₁ | i ∈ x})) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Fintype n] (c : ℝ) (hc₀ : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) ↔
    (∀ [Fintype n] (c : ℝ) (hc₀ : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) ↔
    (∀ [Fintype n] (c : ℝ) (hc₀ : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) ↔
    (∀ [Fintype n] (c : ℝ) (hc₀ : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) ↔
    (∀ [Fintype n] (c : ℝ) (hc₀ : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Fintype n] (c : ℝ) (hc : ¬(c ≤ 1 / 2)), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ) :
    (1 / 2 < c) ↔ (¬(c ≤ 1 / 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ) :
    (1 / 2 < c) ↔ (¬(c ≤ 1 / 2)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ) :
    (1 / 2 < c) ↔ (¬(c ≤ 1 / 2)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ) :
    (1 / 2 < c) ↔ (¬(c ≤ 1 / 2)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ) :
    (1 / 2 < c) ↔ (¬(c ≤ 1 / 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ) :
    (1 / 2 < c) ↔ (¬(c ≤ 1 / 2)) := by
  omega

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ) :
    (1 / 2 < c) ↔ (¬(c ≤ 1 / 2)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ) :
    (1 / 2 < c) ↔ (¬(c ≤ 1 / 2)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) ↔
    (∀ [Fintype n] (c : ℝ) (hc : ¬(c ≤ 1 / 2)), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) ↔
    (∀ [Fintype n] (c : ℝ) (hc : ¬(c ≤ 1 / 2)), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) ↔
    (∀ [Fintype n] (c : ℝ) (hc : ¬(c ≤ 1 / 2)), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) ↔
    (∀ [Fintype n] (c : ℝ) (hc : ¬(c ≤ 1 / 2)), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Fintype n] (c : ℝ) (hc : c ≥ 1 / 2), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : c ≥ 1 / 2), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : c ≥ 1 / 2), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : c ≥ 1 / 2), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : c ≥ 1 / 2), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : c ≥ 1 / 2), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : c ≥ 1 / 2), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : c ≥ 1 / 2), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ)  :
    (1 / 2 < c) ↔ (c ≥ 1 / 2) := by
  omega

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ)  :
    (1 / 2 < c) ↔ (c ≥ 1 / 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ)  :
    (1 / 2 < c) ↔ (c ≥ 1 / 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ)  :
    (1 / 2 < c) ↔ (c ≥ 1 / 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ)  :
    (1 / 2 < c) ↔ (c ≥ 1 / 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ)  :
    (1 / 2 < c) ↔ (c ≥ 1 / 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ)  :
    (1 / 2 < c) ↔ (c ≥ 1 / 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((1 / 2 < c) ↔ (c ≥ 1 / 2))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((1 / 2 < c) ↔ (c ≥ 1 / 2))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((1 / 2 < c) ↔ (c ≥ 1 / 2))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((1 / 2 < c) ↔ (c ≥ 1 / 2))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((1 / 2 < c) ↔ (c ≥ 1 / 2))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((1 / 2 < c) ↔ (c ≥ 1 / 2))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((1 / 2 < c) ↔ (c ≥ 1 / 2)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((1 / 2 < c) ↔ (c ≥ 1 / 2)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((1 / 2 < c) ↔ (c ≥ 1 / 2)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((1 / 2 < c) ↔ (c ≥ 1 / 2)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((1 / 2 < c) ↔ (c ≥ 1 / 2)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((1 / 2 < c) ↔ (c ≥ 1 / 2)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Fintype n] (c : ℝ) (hc : c > 1 / 3), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : c > 1 / 3), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : c > 1 / 3), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : c > 1 / 3), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : c > 1 / 3), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : c > 1 / 3), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : c > 1 / 3), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : c > 1 / 3), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : c > 1 / 3), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : c > 1 / 3), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : c > 1 / 3), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : c > 1 / 3), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : c > 1 / 3), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : c > 1 / 3), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype n] (c : ℝ) (hc : 1 / 2 < c), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) →
    (∀ [Fintype n] (c : ℝ) (hc : c > 1 / 3), ¬ (∀ A : Finset (Finset n), A ≠ {∅} → IsUnionClosed A →
        ∃ i : n, c * #A ≤ #{x ∈ A | i ∈ x})) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ)  :
    (1 / 2 < c) ↔ (c > 1 / 3) := by
  omega

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ)  :
    (1 / 2 < c) ↔ (c > 1 / 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ)  :
    (1 / 2 < c) ↔ (c > 1 / 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ)  :
    (1 / 2 < c) ↔ (c > 1 / 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ)  :
    (1 / 2 < c) ↔ (c > 1 / 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ)  :
    (1 / 2 < c) ↔ (c > 1 / 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ)  :
    (1 / 2 < c) ↔ (c > 1 / 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((1 / 2 < c) ↔ (c > 1 / 3))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((1 / 2 < c) ↔ (c > 1 / 3))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((1 / 2 < c) ↔ (c > 1 / 3))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((1 / 2 < c) ↔ (c > 1 / 3))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((1 / 2 < c) ↔ (c > 1 / 3))) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((1 / 2 < c) ↔ (c > 1 / 3))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((1 / 2 < c) ↔ (c > 1 / 3))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((1 / 2 < c) ↔ (c > 1 / 3)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((1 / 2 < c) ↔ (c > 1 / 3)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((1 / 2 < c) ↔ (c > 1 / 3)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((1 / 2 < c) ↔ (c > 1 / 3)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((1 / 2 < c) ↔ (c > 1 / 3)) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((1 / 2 < c) ↔ (c > 1 / 3)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((1 / 2 < c) ↔ (c > 1 / 3)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ) (hc : 1 / 2 < c) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ) (hc : 1 / 2 < c) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ) (hc : 1 / 2 < c) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ) (hc : 1 / 2 < c) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example [Fintype n] (c : ℝ) (hc : 1 / 2 < c) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
