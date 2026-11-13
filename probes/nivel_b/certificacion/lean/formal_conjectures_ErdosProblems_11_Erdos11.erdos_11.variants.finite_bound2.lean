import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 11

*Reference:* [erdosproblems.com/11](https://www.erdosproblems.com/11)
-/

section

open Filter

namespace Erdos11

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (True))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (True))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (True))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (True))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (True))) :=
  ⟨(50 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (True))) :=
  ⟨(49 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (True))) :=
  ⟨(51 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (True))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (True))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (True)) :=
  ⟨(50 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (True)) :=
  ⟨(49 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (True)) :=
  ⟨(51 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : n ≤ 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n ≤ 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n ≤ 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n ≤ 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n ≤ 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n ≤ 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n ≤ 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n ≤ 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (n ≤ 2^50) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (n ≤ 2^50) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (n ≤ 2^50) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (n ≤ 2^50) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (n ≤ 2^50) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (n ≤ 2^50) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (n ≤ 2^50) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (n ≤ 2^50))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (n ≤ 2^50))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (n ≤ 2^50))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (n ≤ 2^50))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (n ≤ 2^50))) :=
  ⟨(50 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (n ≤ 2^50))) :=
  ⟨(49 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (n ≤ 2^50))) :=
  ⟨(51 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (n ≤ 2^50))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (n ≤ 2^50))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (n ≤ 2^50)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (n ≤ 2^50)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (n ≤ 2^50)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (n ≤ 2^50)) :=
  ⟨(50 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (n ≤ 2^50)) :=
  ⟨(49 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (n ≤ 2^50)) :=
  ⟨(51 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (n ≤ 2^50)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (n ≤ 2^50)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (n ≤ 2^50)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : n < 3^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 3^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 3^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 3^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 3^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 3^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 3^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 3^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 3^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 3^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 3^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 3^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 3^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 3^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 3^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (n < 3^50) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (n < 3^50) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (n < 3^50) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (n < 3^50) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (n < 3^50) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (n < 3^50) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (n < 3^50) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (n < 3^50))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (n < 3^50))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (n < 3^50))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (n < 3^50))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (n < 3^50))) :=
  ⟨(50 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (n < 3^50))) :=
  ⟨(49 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (n < 3^50))) :=
  ⟨(51 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (n < 3^50))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (n < 3^50))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (n < 3^50))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (n < 3^50)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (n < 3^50)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (n < 3^50)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (n < 3^50)) :=
  ⟨(50 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (n < 3^50)) :=
  ⟨(49 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (n < 3^50)) :=
  ⟨(51 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (n < 3^50)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (n < 3^50)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (n < 3^50)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (n < 3^50)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : 2^50 > n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n < 2^50) ↔ (2^50 > n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n < 2^50) ↔ (2^50 > n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n < 2^50) ↔ (2^50 > n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n < 2^50) ↔ (2^50 > n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n < 2^50) ↔ (2^50 > n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n < 2^50) ↔ (2^50 > n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n < 2^50) ↔ (2^50 > n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n < 2^50) ↔ (2^50 > n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (hn : Odd n) (h : 2^50 > n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (hn : Odd n) (h : 2^50 > n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (hn : Odd n) (h : 2^50 > n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (hn : Odd n) (h : 2^50 > n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k₁ l : ℕ , Squarefree k₁ ∧ n = k₁ + 2^l

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔ (∃ k₁ l : ℕ , Squarefree k₁ ∧ n = k₁ + 2^l) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔ (∃ k₁ l : ℕ , Squarefree k₁ ∧ n = k₁ + 2^l) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔ (∃ k₁ l : ℕ , Squarefree k₁ ∧ n = k₁ + 2^l) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔ (∃ k₁ l : ℕ , Squarefree k₁ ∧ n = k₁ + 2^l) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔ (∃ k₁ l : ℕ , Squarefree k₁ ∧ n = k₁ + 2^l) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔ (∃ k₁ l : ℕ , Squarefree k₁ ∧ n = k₁ + 2^l) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔ (∃ k₁ l : ℕ , Squarefree k₁ ∧ n = k₁ + 2^l) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔ (∃ k₁ l : ℕ , Squarefree k₁ ∧ n = k₁ + 2^l) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k₁ l : ℕ , Squarefree k₁ ∧ n = k₁ + 2^l) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k₁ l : ℕ , Squarefree k₁ ∧ n = k₁ + 2^l) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k₁ l : ℕ , Squarefree k₁ ∧ n = k₁ + 2^l) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k₁ l : ℕ , Squarefree k₁ ∧ n = k₁ + 2^l) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (h : n < 2^50) (hn : Odd n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (h : n < 2^50) (hn : Odd n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (h : n < 2^50) (hn : Odd n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (h : n < 2^50) (hn : Odd n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (h : n < 2^50) (hn : Odd n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn₀ : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (hn₀ : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (hn₀ : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (hn₀ : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (hn₀ : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : ¬(2^50 ≤ n)) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n < 2^50) ↔ (¬(2^50 ≤ n)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n < 2^50) ↔ (¬(2^50 ≤ n)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n < 2^50) ↔ (¬(2^50 ≤ n)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n < 2^50) ↔ (¬(2^50 ≤ n)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n < 2^50) ↔ (¬(2^50 ≤ n)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n < 2^50) ↔ (¬(2^50 ≤ n)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n < 2^50) ↔ (¬(2^50 ≤ n)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n < 2^50) ↔ (¬(2^50 ≤ n)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (hn : Odd n) (h : ¬(2^50 ≤ n)) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (hn : Odd n) (h : ¬(2^50 ≤ n)) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (hn : Odd n) (h : ¬(2^50 ≤ n)) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (hn : Odd n) (h : ¬(2^50 ≤ n)) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (2 ≤ n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (2 ≤ n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (2 ≤ n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (2 ≤ n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (2 ≤ n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (2 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : 2^50 ≥ n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : 2^50 ≥ n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : 2^50 ≥ n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : 2^50 ≥ n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : 2^50 ≥ n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : 2^50 ≥ n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : 2^50 ≥ n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : 2^50 ≥ n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (2^50 ≥ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (2^50 ≥ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (2^50 ≥ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (2^50 ≥ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (2^50 ≥ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (2^50 ≥ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (2^50 ≥ n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (2^50 ≥ n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (2^50 ≥ n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (2^50 ≥ n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (2^50 ≥ n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (2^50 ≥ n))) :=
  ⟨(50 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (2^50 ≥ n))) :=
  ⟨(49 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (2^50 ≥ n))) :=
  ⟨(51 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (2^50 ≥ n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (2^50 ≥ n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (2^50 ≥ n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (2^50 ≥ n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (2^50 ≥ n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (2^50 ≥ n)) :=
  ⟨(50 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (2^50 ≥ n)) :=
  ⟨(49 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (2^50 ≥ n)) :=
  ⟨(51 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (2^50 ≥ n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (2^50 ≥ n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (2^50 ≥ n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : 3^50 > n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : 3^50 > n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : 3^50 > n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : 3^50 > n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : 3^50 > n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : 3^50 > n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : 3^50 > n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : 3^50 > n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : 3^50 > n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : 3^50 > n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : 3^50 > n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : 3^50 > n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : 3^50 > n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : 3^50 > n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : 3^50 > n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (3^50 > n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (3^50 > n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (3^50 > n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (3^50 > n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (3^50 > n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (3^50 > n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (3^50 > n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (3^50 > n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (3^50 > n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (3^50 > n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (3^50 > n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (3^50 > n))) :=
  ⟨(50 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (3^50 > n))) :=
  ⟨(49 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (3^50 > n))) :=
  ⟨(51 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (3^50 > n))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (3^50 > n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (3^50 > n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (3^50 > n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (3^50 > n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (3^50 > n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (3^50 > n)) :=
  ⟨(50 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (3^50 > n)) :=
  ⟨(49 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (3^50 > n)) :=
  ⟨(51 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (3^50 > n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (3^50 > n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (3^50 > n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (3^50 > n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : n ≤ 2^50) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n ≤ 2^50) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n ≤ 2^50) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n ≤ 2^50) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n ≤ 2^50) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n ≤ 2^50) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n ≤ 2^50) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n ≤ 2^50) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (n ≤ 2^50) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (n ≤ 2^50) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (n ≤ 2^50) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (n ≤ 2^50) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (n ≤ 2^50) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (n ≤ 2^50) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (n ≤ 2^50) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (n ≤ 2^50))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (n ≤ 2^50))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (n ≤ 2^50))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (n ≤ 2^50))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (n ≤ 2^50))) :=
  ⟨(50 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (n ≤ 2^50))) :=
  ⟨(49 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (n ≤ 2^50))) :=
  ⟨(51 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (n ≤ 2^50))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (n ≤ 2^50))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (n ≤ 2^50)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (n ≤ 2^50)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (n ≤ 2^50)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (n ≤ 2^50)) :=
  ⟨(50 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (n ≤ 2^50)) :=
  ⟨(49 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (n ≤ 2^50)) :=
  ⟨(51 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (n ≤ 2^50)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (n ≤ 2^50)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (n ≤ 2^50)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 2 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 2 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 2 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 2 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 2 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 2 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 2 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 2 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (h : n < 2^50) :
    (1 < n) ↔ (2 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (h : n < 2^50) :
    (1 < n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (h : n < 2^50) :
    (1 < n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (h : n < 2^50) :
    (1 < n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (h : n < 2^50) :
    (1 < n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (h : n < 2^50) :
    (1 < n) ↔ (2 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (h : n < 2^50) :
    (1 < n) ↔ (2 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (n < 2^50) ∧ (¬((1 < n) ↔ (2 < n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (n < 2^50) ∧ (¬((1 < n) ↔ (2 < n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (n < 2^50) ∧ (¬((1 < n) ↔ (2 < n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (n < 2^50) ∧ (¬((1 < n) ↔ (2 < n))) :=
  ⟨(50 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (n < 2^50) ∧ (¬((1 < n) ↔ (2 < n))) :=
  ⟨(49 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (n < 2^50) ∧ (¬((1 < n) ↔ (2 < n))) :=
  ⟨(51 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (n < 2^50) ∧ (¬((1 < n) ↔ (2 < n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (n < 2^50) ∧ (¬((1 < n) ↔ (2 < n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (n < 2^50) ∧ (¬((1 < n) ↔ (2 < n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (2 < n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (2 < n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (2 < n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (2 < n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (2 < n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (2 < n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : n < 3^50) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 3^50) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 3^50) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 3^50) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 3^50) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 3^50) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 3^50) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 3^50) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 3^50) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 3^50) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 3^50) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 3^50) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 3^50) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 3^50) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 3^50) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (n < 3^50) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (n < 3^50) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (n < 3^50) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (n < 3^50) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (n < 3^50) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (n < 3^50) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (n < 3^50) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (n < 3^50))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (n < 3^50))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (n < 3^50))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (n < 3^50))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (n < 3^50))) :=
  ⟨(50 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (n < 3^50))) :=
  ⟨(49 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (n < 3^50))) :=
  ⟨(51 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (n < 3^50))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (n < 3^50))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (n < 3^50))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (n < 3^50)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (n < 3^50)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (n < 3^50)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (n < 3^50)) :=
  ⟨(50 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (n < 3^50)) :=
  ⟨(49 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (n < 3^50)) :=
  ⟨(51 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (n < 3^50)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (n < 3^50)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (n < 3^50)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (n < 3^50)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 2^50) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (True))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (True))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (True))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (True))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (True))) :=
  ⟨(50 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (True))) :=
  ⟨(49 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (True))) :=
  ⟨(51 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (True))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 2^50) ↔ (True))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (True)) :=
  ⟨(50 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (True)) :=
  ⟨(49 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (True)) :=
  ⟨(51 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 2^50) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (h : n < 2^50) (hn' : 1 < n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
