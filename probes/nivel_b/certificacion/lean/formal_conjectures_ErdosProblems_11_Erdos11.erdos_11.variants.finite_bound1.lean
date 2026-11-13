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
  ∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (True))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (True))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (True))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (True))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (True))) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (True))) :=
  ⟨(11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (True))) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (True))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (True))) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (True))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (True))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (True)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (True)) :=
  ⟨(11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (True)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (True)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (True)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : n ≤ 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n ≤ 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n ≤ 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n ≤ 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n ≤ 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n ≤ 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n ≤ 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n ≤ 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (n ≤ 10^7) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (n ≤ 10^7) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (n ≤ 10^7) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (n ≤ 10^7) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (n ≤ 10^7) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (n ≤ 10^7) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (n ≤ 10^7) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (n ≤ 10^7))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (n ≤ 10^7))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (n ≤ 10^7))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (n ≤ 10^7))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (n ≤ 10^7))) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (n ≤ 10^7))) :=
  ⟨(11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (n ≤ 10^7))) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (n ≤ 10^7))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (n ≤ 10^7))) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (n ≤ 10^7))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (n ≤ 10^7))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (n ≤ 10^7)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (n ≤ 10^7)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (n ≤ 10^7)) :=
  ⟨(11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (n ≤ 10^7)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (n ≤ 10^7)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (n ≤ 10^7)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (n ≤ 10^7)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (n ≤ 10^7)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (n ≤ 10^7)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (n ≤ 10^7)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (n ≤ 10^7)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : n < 11^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 11^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 11^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 11^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 11^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 11^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 11^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 11^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 11^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 11^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 11^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 11^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 11^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 11^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 11^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (n < 11^7) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (n < 11^7) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (n < 11^7) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (n < 11^7) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (n < 11^7) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (n < 11^7) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (n < 11^7) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (n < 11^7))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (n < 11^7))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (n < 11^7))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (n < 11^7))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (n < 11^7))) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (n < 11^7))) :=
  ⟨(11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (n < 11^7))) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (n < 11^7))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (n < 11^7))) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (n < 11^7))) :=
  ⟨(12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (n < 11^7))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (n < 11^7))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (n < 11^7)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (n < 11^7)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (n < 11^7)) :=
  ⟨(11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (n < 11^7)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (n < 11^7)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (n < 11^7)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (n < 11^7)) :=
  ⟨(12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (n < 11^7)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (n < 11^7)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (n < 11^7)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (n < 11^7)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (n < 11^7)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : 10^7 > n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n < 10^7) ↔ (10^7 > n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n < 10^7) ↔ (10^7 > n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n < 10^7) ↔ (10^7 > n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n < 10^7) ↔ (10^7 > n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n < 10^7) ↔ (10^7 > n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n < 10^7) ↔ (10^7 > n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n < 10^7) ↔ (10^7 > n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n < 10^7) ↔ (10^7 > n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (hn : Odd n) (h : 10^7 > n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (hn : Odd n) (h : 10^7 > n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (hn : Odd n) (h : 10^7 > n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (hn : Odd n) (h : 10^7 > n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k₁ l : ℕ , Squarefree k₁ ∧ n = k₁ + 2^l

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
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k₁ l : ℕ , Squarefree k₁ ∧ n = k₁ + 2^l) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k₁ l : ℕ , Squarefree k₁ ∧ n = k₁ + 2^l) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k₁ l : ℕ , Squarefree k₁ ∧ n = k₁ + 2^l) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k₁ l : ℕ , Squarefree k₁ ∧ n = k₁ + 2^l) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (h : n < 10^7) (hn : Odd n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (h : n < 10^7) (hn : Odd n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (h : n < 10^7) (hn : Odd n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (h : n < 10^7) (hn : Odd n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (h : n < 10^7) (hn : Odd n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn₀ : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (hn₀ : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (hn₀ : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (hn₀ : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (hn₀ : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : ¬(10^7 ≤ n)) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n < 10^7) ↔ (¬(10^7 ≤ n)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n < 10^7) ↔ (¬(10^7 ≤ n)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n < 10^7) ↔ (¬(10^7 ≤ n)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n < 10^7) ↔ (¬(10^7 ≤ n)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n < 10^7) ↔ (¬(10^7 ≤ n)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n < 10^7) ↔ (¬(10^7 ≤ n)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n < 10^7) ↔ (¬(10^7 ≤ n)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (n < 10^7) ↔ (¬(10^7 ≤ n)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (hn : Odd n) (h : ¬(10^7 ≤ n)) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (hn : Odd n) (h : ¬(10^7 ≤ n)) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (hn : Odd n) (h : ¬(10^7 ≤ n)) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (hn : Odd n) (h : ¬(10^7 ≤ n)) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

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
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) ↔
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : 10^7 ≥ n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : 10^7 ≥ n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : 10^7 ≥ n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : 10^7 ≥ n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : 10^7 ≥ n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : 10^7 ≥ n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : 10^7 ≥ n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : 10^7 ≥ n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (10^7 ≥ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (10^7 ≥ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (10^7 ≥ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (10^7 ≥ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (10^7 ≥ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (10^7 ≥ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (10^7 ≥ n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (10^7 ≥ n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (10^7 ≥ n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (10^7 ≥ n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (10^7 ≥ n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (10^7 ≥ n))) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (10^7 ≥ n))) :=
  ⟨(11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (10^7 ≥ n))) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (10^7 ≥ n))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (10^7 ≥ n))) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (10^7 ≥ n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (10^7 ≥ n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (10^7 ≥ n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (10^7 ≥ n)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (10^7 ≥ n)) :=
  ⟨(11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (10^7 ≥ n)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (10^7 ≥ n)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (10^7 ≥ n)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (10^7 ≥ n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (10^7 ≥ n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (10^7 ≥ n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (10^7 ≥ n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (10^7 ≥ n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : 11^7 > n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : 11^7 > n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : 11^7 > n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : 11^7 > n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : 11^7 > n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : 11^7 > n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : 11^7 > n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : 11^7 > n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : 11^7 > n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : 11^7 > n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : 11^7 > n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : 11^7 > n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : 11^7 > n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : 11^7 > n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : 11^7 > n) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (11^7 > n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (11^7 > n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (11^7 > n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (11^7 > n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (11^7 > n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (11^7 > n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (11^7 > n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (11^7 > n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (11^7 > n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (11^7 > n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (11^7 > n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (11^7 > n))) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (11^7 > n))) :=
  ⟨(11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (11^7 > n))) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (11^7 > n))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (11^7 > n))) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (11^7 > n))) :=
  ⟨(12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (11^7 > n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (11^7 > n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (11^7 > n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (11^7 > n)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (11^7 > n)) :=
  ⟨(11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (11^7 > n)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (11^7 > n)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (11^7 > n)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (11^7 > n)) :=
  ⟨(12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (11^7 > n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (11^7 > n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (11^7 > n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (11^7 > n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (11^7 > n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : n ≤ 10^7) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n ≤ 10^7) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n ≤ 10^7) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n ≤ 10^7) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n ≤ 10^7) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n ≤ 10^7) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n ≤ 10^7) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n ≤ 10^7) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (n ≤ 10^7) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (n ≤ 10^7) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (n ≤ 10^7) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (n ≤ 10^7) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (n ≤ 10^7) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (n ≤ 10^7) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (n ≤ 10^7) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (n ≤ 10^7))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (n ≤ 10^7))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (n ≤ 10^7))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (n ≤ 10^7))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (n ≤ 10^7))) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (n ≤ 10^7))) :=
  ⟨(11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (n ≤ 10^7))) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (n ≤ 10^7))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (n ≤ 10^7))) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (n ≤ 10^7))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (n ≤ 10^7))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (n ≤ 10^7)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (n ≤ 10^7)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (n ≤ 10^7)) :=
  ⟨(11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (n ≤ 10^7)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (n ≤ 10^7)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (n ≤ 10^7)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (n ≤ 10^7)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (n ≤ 10^7)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (n ≤ 10^7)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (n ≤ 10^7)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (n ≤ 10^7)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 2 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 2 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 2 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 2 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 2 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 2 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 2 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 2 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (h : n < 10^7) :
    (1 < n) ↔ (2 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (h : n < 10^7) :
    (1 < n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (h : n < 10^7) :
    (1 < n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (h : n < 10^7) :
    (1 < n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (h : n < 10^7) :
    (1 < n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (h : n < 10^7) :
    (1 < n) ↔ (2 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (h : n < 10^7) :
    (1 < n) ↔ (2 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (n < 10^7) ∧ (¬((1 < n) ↔ (2 < n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (n < 10^7) ∧ (¬((1 < n) ↔ (2 < n))) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (n < 10^7) ∧ (¬((1 < n) ↔ (2 < n))) :=
  ⟨(11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (n < 10^7) ∧ (¬((1 < n) ↔ (2 < n))) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (n < 10^7) ∧ (¬((1 < n) ↔ (2 < n))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (n < 10^7) ∧ (¬((1 < n) ↔ (2 < n))) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (n < 10^7) ∧ (¬((1 < n) ↔ (2 < n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (n < 10^7) ∧ (¬((1 < n) ↔ (2 < n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (n < 10^7) ∧ (¬((1 < n) ↔ (2 < n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (n < 10^7) ∧ (¬((1 < n) ↔ (2 < n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (n < 10^7) ∧ (¬((1 < n) ↔ (2 < n))) :=
  ⟨(5 : ℕ), by norm_num⟩

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
  ∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : n < 11^7) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 11^7) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 11^7) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 11^7) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 11^7) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 11^7) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 11^7) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 11^7) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 11^7) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 11^7) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 11^7) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 11^7) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 11^7) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 11^7) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 11^7) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (n < 11^7) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (n < 11^7) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (n < 11^7) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (n < 11^7) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (n < 11^7) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (n < 11^7) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (n < 11^7) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (n < 11^7))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (n < 11^7))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (n < 11^7))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (n < 11^7))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (n < 11^7))) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (n < 11^7))) :=
  ⟨(11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (n < 11^7))) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (n < 11^7))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (n < 11^7))) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (n < 11^7))) :=
  ⟨(12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (n < 11^7))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (n < 11^7))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (n < 11^7)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (n < 11^7)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (n < 11^7)) :=
  ⟨(11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (n < 11^7)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (n < 11^7)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (n < 11^7)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (n < 11^7)) :=
  ⟨(12 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (n < 11^7)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (n < 11^7)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (n < 11^7)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (n < 11^7)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (n < 11^7)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : Odd n) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : Odd n) (hn' : 2 ≤ n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) →
    (∀ (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n), ∃ k l : ℕ , Squarefree k ∧ n = k + 2^l) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (hn' : 1 < n) :
    (n < 10^7) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (True))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (True))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (True))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (True))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (True))) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (True))) :=
  ⟨(11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (True))) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (True))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (True))) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (True))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (Odd n) ∧ (1 < n) ∧ (¬((n < 10^7) ↔ (True))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (True)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (True)) :=
  ⟨(11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (True)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (True)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (True)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10^7) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
