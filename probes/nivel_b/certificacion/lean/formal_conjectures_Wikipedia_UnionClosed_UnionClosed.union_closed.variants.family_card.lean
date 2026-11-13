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
  ∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) →
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) →
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) →
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) →
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) →
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) →
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) →
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) :
    (#A ≤ 50) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) :
    (#A ≤ 50) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) :
    (#A ≤ 50) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) :
    (#A ≤ 50) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) :
    (#A ≤ 50) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) :
    (#A ≤ 50) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) :
    (#A ≤ 50) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : (A ≠ {∅}) ∧ (IsUnionClosed A) ∧ (¬((#A ≤ 50) ↔ (True))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (A ≠ {∅}) ∧ (IsUnionClosed A) ∧ (¬((#A ≤ 50) ↔ (True))) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((#A ≤ 50) ↔ (True)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((#A ≤ 50) ↔ (True)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A < 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) →
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A < 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) →
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A < 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) →
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A < 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) →
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A < 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) →
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A < 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) →
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A < 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) →
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A < 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) :
    (#A ≤ 50) ↔ (#A < 50) := by
  omega

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) :
    (#A ≤ 50) ↔ (#A < 50) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) :
    (#A ≤ 50) ↔ (#A < 50) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) :
    (#A ≤ 50) ↔ (#A < 50) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) :
    (#A ≤ 50) ↔ (#A < 50) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) :
    (#A ≤ 50) ↔ (#A < 50) := by
  simp_all

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) :
    (#A ≤ 50) ↔ (#A < 50) := by
  plausible

set_option maxHeartbeats 200000 in
example : (A ≠ {∅}) ∧ (IsUnionClosed A) ∧ (¬((#A ≤ 50) ↔ (#A < 50))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (A ≠ {∅}) ∧ (IsUnionClosed A) ∧ (¬((#A ≤ 50) ↔ (#A < 50))) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((#A ≤ 50) ↔ (#A < 50)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((#A ≤ 50) ↔ (#A < 50)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 51), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 51), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) →
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 51), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) →
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 51), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) →
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 51), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) →
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 51), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) →
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 51), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) →
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 51), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) →
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) :
    (#A ≤ 50) ↔ (#A ≤ 51) := by
  omega

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) :
    (#A ≤ 50) ↔ (#A ≤ 51) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) :
    (#A ≤ 50) ↔ (#A ≤ 51) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) :
    (#A ≤ 50) ↔ (#A ≤ 51) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) :
    (#A ≤ 50) ↔ (#A ≤ 51) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) :
    (#A ≤ 50) ↔ (#A ≤ 51) := by
  simp_all

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) :
    (#A ≤ 50) ↔ (#A ≤ 51) := by
  plausible

set_option maxHeartbeats 200000 in
example : (A ≠ {∅}) ∧ (IsUnionClosed A) ∧ (¬((#A ≤ 50) ↔ (#A ≤ 51))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (A ≠ {∅}) ∧ (IsUnionClosed A) ∧ (¬((#A ≤ 50) ↔ (#A ≤ 51))) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((#A ≤ 50) ↔ (#A ≤ 51)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((#A ≤ 50) ↔ (#A ≤ 51)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : 50 ≥ #A), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}

set_option maxHeartbeats 200000 in
example [Nonempty n] :
    (#A ≤ 50) ↔ (50 ≥ #A) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example [Nonempty n] :
    (#A ≤ 50) ↔ (50 ≥ #A) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example [Nonempty n] :
    (#A ≤ 50) ↔ (50 ≥ #A) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example [Nonempty n] :
    (#A ≤ 50) ↔ (50 ≥ #A) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example [Nonempty n] :
    (#A ≤ 50) ↔ (50 ≥ #A) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example [Nonempty n] :
    (#A ≤ 50) ↔ (50 ≥ #A) := by
  omega

set_option maxHeartbeats 200000 in
example [Nonempty n] :
    (#A ≤ 50) ↔ (50 ≥ #A) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example [Nonempty n] :
    (#A ≤ 50) ↔ (50 ≥ #A) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) ↔
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : 50 ≥ #A), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) ↔
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : 50 ≥ #A), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) ↔
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : 50 ≥ #A), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) ↔
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : 50 ≥ #A), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i₁ : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i₁ ∈ x}

set_option maxHeartbeats 200000 in
example [Nonempty n] :
    (∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) ↔ (∃ i₁ : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i₁ ∈ x}) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example [Nonempty n] :
    (∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) ↔ (∃ i₁ : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i₁ ∈ x}) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example [Nonempty n] :
    (∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) ↔ (∃ i₁ : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i₁ ∈ x}) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example [Nonempty n] :
    (∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) ↔ (∃ i₁ : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i₁ ∈ x}) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example [Nonempty n] :
    (∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) ↔ (∃ i₁ : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i₁ ∈ x}) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example [Nonempty n] :
    (∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) ↔ (∃ i₁ : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i₁ ∈ x}) := by
  omega

set_option maxHeartbeats 200000 in
example [Nonempty n] :
    (∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) ↔ (∃ i₁ : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i₁ ∈ x}) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example [Nonempty n] :
    (∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) ↔ (∃ i₁ : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i₁ ∈ x}) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) ↔
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i₁ : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i₁ ∈ x}) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) ↔
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i₁ : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i₁ ∈ x}) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) ↔
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i₁ : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i₁ ∈ x}) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) ↔
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i₁ : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i₁ ∈ x}) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Nonempty n] (h_union_closed : IsUnionClosed A) (h_ne_singleton_empty : A ≠ {∅}) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) ↔
    (∀ [Nonempty n] (h_union_closed : IsUnionClosed A) (h_ne_singleton_empty : A ≠ {∅}) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) ↔
    (∀ [Nonempty n] (h_union_closed : IsUnionClosed A) (h_ne_singleton_empty : A ≠ {∅}) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) ↔
    (∀ [Nonempty n] (h_union_closed : IsUnionClosed A) (h_ne_singleton_empty : A ≠ {∅}) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) ↔
    (∀ [Nonempty n] (h_union_closed : IsUnionClosed A) (h_ne_singleton_empty : A ≠ {∅}) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Nonempty n] (h_ne_singleton_empty₀ : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) ↔
    (∀ [Nonempty n] (h_ne_singleton_empty₀ : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) ↔
    (∀ [Nonempty n] (h_ne_singleton_empty₀ : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) ↔
    (∀ [Nonempty n] (h_ne_singleton_empty₀ : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) ↔
    (∀ [Nonempty n] (h_ne_singleton_empty₀ : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : ¬(50 < #A)), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}

set_option maxHeartbeats 200000 in
example [Nonempty n] :
    (#A ≤ 50) ↔ (¬(50 < #A)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example [Nonempty n] :
    (#A ≤ 50) ↔ (¬(50 < #A)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example [Nonempty n] :
    (#A ≤ 50) ↔ (¬(50 < #A)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example [Nonempty n] :
    (#A ≤ 50) ↔ (¬(50 < #A)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example [Nonempty n] :
    (#A ≤ 50) ↔ (¬(50 < #A)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example [Nonempty n] :
    (#A ≤ 50) ↔ (¬(50 < #A)) := by
  omega

set_option maxHeartbeats 200000 in
example [Nonempty n] :
    (#A ≤ 50) ↔ (¬(50 < #A)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example [Nonempty n] :
    (#A ≤ 50) ↔ (¬(50 < #A)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) ↔
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : ¬(50 < #A)), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) ↔
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : ¬(50 < #A)), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) ↔
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : ¬(50 < #A)), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) ↔
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : ¬(50 < #A)), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : 50 > #A), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) →
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : 50 > #A), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) →
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : 50 > #A), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) →
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : 50 > #A), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) →
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : 50 > #A), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) →
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : 50 > #A), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) →
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : 50 > #A), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) →
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : 50 > #A), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) :
    (#A ≤ 50) ↔ (50 > #A) := by
  omega

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) :
    (#A ≤ 50) ↔ (50 > #A) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) :
    (#A ≤ 50) ↔ (50 > #A) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) :
    (#A ≤ 50) ↔ (50 > #A) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) :
    (#A ≤ 50) ↔ (50 > #A) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) :
    (#A ≤ 50) ↔ (50 > #A) := by
  simp_all

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) :
    (#A ≤ 50) ↔ (50 > #A) := by
  plausible

set_option maxHeartbeats 200000 in
example : (A ≠ {∅}) ∧ (IsUnionClosed A) ∧ (¬((#A ≤ 50) ↔ (50 > #A))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (A ≠ {∅}) ∧ (IsUnionClosed A) ∧ (¬((#A ≤ 50) ↔ (50 > #A))) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((#A ≤ 50) ↔ (50 > #A)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((#A ≤ 50) ↔ (50 > #A)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : 51 ≥ #A), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : 51 ≥ #A), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) →
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : 51 ≥ #A), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) →
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : 51 ≥ #A), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) →
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : 51 ≥ #A), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) →
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : 51 ≥ #A), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) →
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : 51 ≥ #A), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) →
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : 51 ≥ #A), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) →
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) :
    (#A ≤ 50) ↔ (51 ≥ #A) := by
  omega

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) :
    (#A ≤ 50) ↔ (51 ≥ #A) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) :
    (#A ≤ 50) ↔ (51 ≥ #A) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) :
    (#A ≤ 50) ↔ (51 ≥ #A) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) :
    (#A ≤ 50) ↔ (51 ≥ #A) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) :
    (#A ≤ 50) ↔ (51 ≥ #A) := by
  simp_all

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) :
    (#A ≤ 50) ↔ (51 ≥ #A) := by
  plausible

set_option maxHeartbeats 200000 in
example : (A ≠ {∅}) ∧ (IsUnionClosed A) ∧ (¬((#A ≤ 50) ↔ (51 ≥ #A))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (A ≠ {∅}) ∧ (IsUnionClosed A) ∧ (¬((#A ≤ 50) ↔ (51 ≥ #A))) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((#A ≤ 50) ↔ (51 ≥ #A)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((#A ≤ 50) ↔ (51 ≥ #A)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Nonempty n] (h_union_closed : IsUnionClosed A) (h_ne_singleton_empty : A ≠ {∅}), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_union_closed : IsUnionClosed A) (h_ne_singleton_empty : A ≠ {∅}), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) →
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_union_closed : IsUnionClosed A) (h_ne_singleton_empty : A ≠ {∅}), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) →
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_union_closed : IsUnionClosed A) (h_ne_singleton_empty : A ≠ {∅}), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) →
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_union_closed : IsUnionClosed A) (h_ne_singleton_empty : A ≠ {∅}), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) →
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_union_closed : IsUnionClosed A) (h_ne_singleton_empty : A ≠ {∅}), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) →
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_union_closed : IsUnionClosed A) (h_ne_singleton_empty : A ≠ {∅}), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) →
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [Nonempty n] (h_union_closed : IsUnionClosed A) (h_ne_singleton_empty : A ≠ {∅}), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) →
    (∀ [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50), ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) :
    (#A ≤ 50) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) :
    (#A ≤ 50) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) :
    (#A ≤ 50) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) :
    (#A ≤ 50) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) :
    (#A ≤ 50) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) :
    (#A ≤ 50) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) :
    (#A ≤ 50) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : (A ≠ {∅}) ∧ (IsUnionClosed A) ∧ (¬((#A ≤ 50) ↔ (True))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (A ≠ {∅}) ∧ (IsUnionClosed A) ∧ (¬((#A ≤ 50) ↔ (True))) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((#A ≤ 50) ↔ (True)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((#A ≤ 50) ↔ (True)) :=
  by decide

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example [Nonempty n] (h_ne_singleton_empty : A ≠ {∅}) (h_union_closed : IsUnionClosed A) (hA : #A ≤ 50) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
