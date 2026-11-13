import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 137

*References:*
- [erdosproblems.com/137](https://www.erdosproblems.com/137)
-/

section

namespace Erdos137

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l) :
    (k ≥ 2) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l) :
    (k ≥ 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l) :
    (k ≥ 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l) :
    (k ≥ 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l) :
    (k ≥ 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l) :
    (k ≥ 2) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l) :
    (k ≥ 2) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (True))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (True))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (True))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (True))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (True))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (True))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (True))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (True))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (True))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (True))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (True))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (True))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (True))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (True))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (True))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (True))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (True))) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (True))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (True))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k > 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : k > 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : k > 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : k > 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : k > 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : k > 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : k > 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : k > 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l) :
    (k ≥ 2) ↔ (k > 2) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l) :
    (k ≥ 2) ↔ (k > 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l) :
    (k ≥ 2) ↔ (k > 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l) :
    (k ≥ 2) ↔ (k > 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l) :
    (k ≥ 2) ↔ (k > 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l) :
    (k ≥ 2) ↔ (k > 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l) :
    (k ≥ 2) ↔ (k > 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k > 2))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k > 2))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k > 2))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k > 2))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k > 2))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k > 2))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k > 2))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k > 2))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k > 2))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k > 2))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k > 2))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k > 2))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k > 2))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k > 2))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k > 2))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k > 2))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k > 2))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k > 2))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k > 2))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k > 2))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k > 2))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k > 2))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k > 2))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k > 2))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k > 2))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k > 2))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k > 2))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k > 2))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k > 2))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k > 2))) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k > 2))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k > 2))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k > 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k > 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k > 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k > 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k > 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k > 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 3) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : k ≥ 3) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : k ≥ 3) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : k ≥ 3) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : k ≥ 3) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : k ≥ 3) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : k ≥ 3) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : k ≥ 3) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l) :
    (k ≥ 2) ↔ (k ≥ 3) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l) :
    (k ≥ 2) ↔ (k ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l) :
    (k ≥ 2) ↔ (k ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l) :
    (k ≥ 2) ↔ (k ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l) :
    (k ≥ 2) ↔ (k ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l) :
    (k ≥ 2) ↔ (k ≥ 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l) :
    (k ≥ 2) ↔ (k ≥ 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 3))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 3))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 3))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 3))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 3))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 3))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 3))) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 3))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 3))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 3))) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 3))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 3))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 3))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 3))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 3))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 3))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 3))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 3))) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 3))) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 3))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 3))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 3))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 3))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 3))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 3))) :=
  ⟨(4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 3))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 3))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 3))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 3))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 3))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 3))) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 3))) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k ≥ 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k ≥ 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k ≥ 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k ≥ 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k ≥ 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k ≥ 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k ≥ 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) :
    (k ≥ 2) ↔ (2 ≤ k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) :
    (k ≥ 2) ↔ (2 ≤ k) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) :
    (k ≥ 2) ↔ (2 ≤ k) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) :
    (k ≥ 2) ↔ (2 ≤ k) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) :
    (k ≥ 2) ↔ (2 ≤ k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) :
    (k ≥ 2) ↔ (2 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) :
    (k ≥ 2) ↔ (2 ≤ k) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) :
    (k ≥ 2) ↔ (2 ≤ k) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) ↔
    (∀ (k : ℕ) (hk : 2 ≤ k) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) ↔
    (∀ (k : ℕ) (hk : 2 ≤ k) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) ↔
    (∀ (k : ℕ) (hk : 2 ≤ k) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) ↔
    (∀ (k : ℕ) (hk : 2 ≤ k) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk₀ : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) ↔
    (∀ (k : ℕ) (hk₀ : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) ↔
    (∀ (k : ℕ) (hk₀ : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) ↔
    (∀ (k : ℕ) (hk₀ : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) ↔
    (∀ (k : ℕ) (hk₀ : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : ¬(k < 2)) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) :
    (k ≥ 2) ↔ (¬(k < 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) :
    (k ≥ 2) ↔ (¬(k < 2)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) :
    (k ≥ 2) ↔ (¬(k < 2)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) :
    (k ≥ 2) ↔ (¬(k < 2)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) :
    (k ≥ 2) ↔ (¬(k < 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) :
    (k ≥ 2) ↔ (¬(k < 2)) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) :
    (k ≥ 2) ↔ (¬(k < 2)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) :
    (k ≥ 2) ↔ (¬(k < 2)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) ↔
    (∀ (k : ℕ) (hk : ¬(k < 2)) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) ↔
    (∀ (k : ℕ) (hk : ¬(k < 2)) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) ↔
    (∀ (k : ℕ) (hk : ¬(k < 2)) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) ↔
    (∀ (k : ℕ) (hk : ¬(k < 2)) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k > 1) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) :
    (k ≥ 2) ↔ (k > 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) :
    (k ≥ 2) ↔ (k > 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) :
    (k ≥ 2) ↔ (k > 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) :
    (k ≥ 2) ↔ (k > 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) :
    (k ≥ 2) ↔ (k > 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) :
    (k ≥ 2) ↔ (k > 1) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) :
    (k ≥ 2) ↔ (k > 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) :
    (k ≥ 2) ↔ (k > 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) ↔
    (∀ (k : ℕ) (hk : k > 1) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) ↔
    (∀ (k : ℕ) (hk : k > 1) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) ↔
    (∀ (k : ℕ) (hk : k > 1) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) ↔
    (∀ (k : ℕ) (hk : k > 1) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 < k) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : 2 < k) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : 2 < k) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : 2 < k) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : 2 < k) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : 2 < k) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : 2 < k) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : 2 < k) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l) :
    (k ≥ 2) ↔ (2 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l) :
    (k ≥ 2) ↔ (2 < k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l) :
    (k ≥ 2) ↔ (2 < k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l) :
    (k ≥ 2) ↔ (2 < k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l) :
    (k ≥ 2) ↔ (2 < k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l) :
    (k ≥ 2) ↔ (2 < k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l) :
    (k ≥ 2) ↔ (2 < k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (2 < k))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (2 < k))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (2 < k))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (2 < k))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (2 < k))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (2 < k))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (2 < k))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (2 < k))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (2 < k))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (2 < k))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (2 < k))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (2 < k))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (2 < k))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (2 < k))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (2 < k))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (2 < k))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (2 < k))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (2 < k))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (2 < k))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (2 < k))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (2 < k))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (2 < k))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (2 < k))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (2 < k))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (2 < k))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (2 < k))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (2 < k))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (2 < k))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (2 < k))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (2 < k))) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (2 < k))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (2 < k))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (2 < k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (2 < k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (2 < k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (2 < k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (2 < k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (2 < k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l) :
    (k ≥ 2) ↔ (3 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l) :
    (k ≥ 2) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l) :
    (k ≥ 2) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l) :
    (k ≥ 2) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l) :
    (k ≥ 2) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l) :
    (k ≥ 2) ↔ (3 ≤ k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l) :
    (k ≥ 2) ↔ (3 ≤ k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (3 ≤ k))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (3 ≤ k))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (3 ≤ k))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (3 ≤ k))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (3 ≤ k))) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (3 ≤ k))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (3 ≤ k))) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (3 ≤ k))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (3 ≤ k))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (3 ≤ k))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (3 ≤ k))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (3 ≤ k))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (3 ≤ k))) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (3 ≤ k))) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (3 ≤ k))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (3 ≤ k))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (3 ≤ k))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (3 ≤ k))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (3 ≤ k))) :=
  ⟨(4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (3 ≤ k))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (3 ≤ k))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (3 ≤ k))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (3 ≤ k))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (3 ≤ k))) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (3 ≤ k))) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (3 ≤ k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (3 ≤ k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (3 ≤ k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (3 ≤ k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (3 ≤ k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (3 ≤ k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (3 ≤ k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 1) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 1) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 1) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 1) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 1) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 1) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 1) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 1) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l) :
    (k ≥ 2) ↔ (k ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l) :
    (k ≥ 2) ↔ (k ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l) :
    (k ≥ 2) ↔ (k ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l) :
    (k ≥ 2) ↔ (k ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l) :
    (k ≥ 2) ↔ (k ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l) :
    (k ≥ 2) ↔ (k ≥ 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l) :
    (k ≥ 2) ↔ (k ≥ 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 1))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 1))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 1))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 1))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 1))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 1))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 1))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 1))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 1))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 1))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 1))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 1))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 1))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 1))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 1))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 1))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 1))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 1))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 1))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 1))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 1))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 1))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 1))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 1))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 1))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 1))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 1))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 1))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 1))) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 1))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (2 ≤ l) ∧ (¬((k ≥ 2) ↔ (k ≥ 1))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k ≥ 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k ≥ 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k ≥ 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k ≥ 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k ≥ 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k ≥ 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k > 1) (n : ℕ) (x l : ℕ) (hl : 2 < l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : k > 1) (n : ℕ) (x l : ℕ) (hl : 2 < l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : k > 1) (n : ℕ) (x l : ℕ) (hl : 2 < l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : k > 1) (n : ℕ) (x l : ℕ) (hl : 2 < l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : k > 1) (n : ℕ) (x l : ℕ) (hl : 2 < l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : k > 1) (n : ℕ) (x l : ℕ) (hl : 2 < l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : k > 1) (n : ℕ) (x l : ℕ) (hl : 2 < l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : k > 1) (n : ℕ) (x l : ℕ) (hl : 2 < l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hk : k ≥ 2) :
    (2 ≤ l) ↔ (2 < l) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hk : k ≥ 2) :
    (2 ≤ l) ↔ (2 < l) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hk : k ≥ 2) :
    (2 ≤ l) ↔ (2 < l) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hk : k ≥ 2) :
    (2 ≤ l) ↔ (2 < l) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hk : k ≥ 2) :
    (2 ≤ l) ↔ (2 < l) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hk : k ≥ 2) :
    (2 ≤ l) ↔ (2 < l) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hk : k ≥ 2) :
    (2 ≤ l) ↔ (2 < l) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (2 < l))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (2 < l))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (2 < l))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (2 < l))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (2 < l))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (2 < l))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (2 < l))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (2 < l))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (2 < l))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (2 < l))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (2 < l))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (2 < l))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (2 < l))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (2 < l))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (2 < l))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (2 < l))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (2 < l))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (2 < l))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (2 < l))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (2 < l))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (2 < l))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (2 < l))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (2 < l))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (2 < l))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (2 < l))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (2 < l))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (2 < l))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (2 < l))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (2 < l))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (2 < l))) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (2 < l))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (2 < l))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ), ¬((2 ≤ l) ↔ (2 < l)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ), ¬((2 ≤ l) ↔ (2 < l)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ), ¬((2 ≤ l) ↔ (2 < l)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ), ¬((2 ≤ l) ↔ (2 < l)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ), ¬((2 ≤ l) ↔ (2 < l)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ), ¬((2 ≤ l) ↔ (2 < l)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k > 1) (n : ℕ) (x l : ℕ) (hl : 3 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : k > 1) (n : ℕ) (x l : ℕ) (hl : 3 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : k > 1) (n : ℕ) (x l : ℕ) (hl : 3 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : k > 1) (n : ℕ) (x l : ℕ) (hl : 3 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : k > 1) (n : ℕ) (x l : ℕ) (hl : 3 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : k > 1) (n : ℕ) (x l : ℕ) (hl : 3 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : k > 1) (n : ℕ) (x l : ℕ) (hl : 3 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) →
    (∀ (k : ℕ) (hk : k > 1) (n : ℕ) (x l : ℕ) (hl : 3 ≤ l), (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hk : k ≥ 2) :
    (2 ≤ l) ↔ (3 ≤ l) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hk : k ≥ 2) :
    (2 ≤ l) ↔ (3 ≤ l) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hk : k ≥ 2) :
    (2 ≤ l) ↔ (3 ≤ l) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hk : k ≥ 2) :
    (2 ≤ l) ↔ (3 ≤ l) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hk : k ≥ 2) :
    (2 ≤ l) ↔ (3 ≤ l) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hk : k ≥ 2) :
    (2 ≤ l) ↔ (3 ≤ l) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hk : k ≥ 2) :
    (2 ≤ l) ↔ (3 ≤ l) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (3 ≤ l))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (3 ≤ l))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (3 ≤ l))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (3 ≤ l))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (3 ≤ l))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (3 ≤ l))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (3 ≤ l))) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (3 ≤ l))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (3 ≤ l))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (3 ≤ l))) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (3 ≤ l))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (3 ≤ l))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (3 ≤ l))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (3 ≤ l))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (3 ≤ l))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (3 ≤ l))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (3 ≤ l))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (3 ≤ l))) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (3 ≤ l))) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (3 ≤ l))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (3 ≤ l))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (3 ≤ l))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (3 ≤ l))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (3 ≤ l))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (3 ≤ l))) :=
  ⟨(4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (3 ≤ l))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (3 ≤ l))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (3 ≤ l))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (3 ≤ l))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (3 ≤ l))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (3 ≤ l))) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (l : ℕ), (k ≥ 2) ∧ (¬((2 ≤ l) ↔ (3 ≤ l))) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ), ¬((2 ≤ l) ↔ (3 ≤ l)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ), ¬((2 ≤ l) ↔ (3 ≤ l)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ), ¬((2 ≤ l) ↔ (3 ≤ l)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ), ¬((2 ≤ l) ↔ (3 ≤ l)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ), ¬((2 ≤ l) ↔ (3 ≤ l)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ), ¬((2 ≤ l) ↔ (3 ≤ l)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ), ¬((2 ≤ l) ↔ (3 ≤ l)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hk : k ≥ 2) (hl : 2 ≤ l) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hk : k ≥ 2) (hl : 2 ≤ l) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hk : k ≥ 2) (hl : 2 ≤ l) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hk : k ≥ 2) (hl : 2 ≤ l) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (n : ℕ) (x l : ℕ) (hk : k ≥ 2) (hl : 2 ≤ l) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
