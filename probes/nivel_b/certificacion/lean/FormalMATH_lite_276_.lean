import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

open Nat

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m n : ℕ} (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) →
    (∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) →
    (∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) →
    (∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) →
    (∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) →
    (∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) →
    (∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) →
    (∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn : 0 < n) :
    (0 < m) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn : 0 < n) :
    (0 < m) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn : 0 < n) :
    (0 < m) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn : 0 < n) :
    (0 < m) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn : 0 < n) :
    (0 < m) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn : 0 < n) :
    (0 < m) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hn : 0 < n) :
    (0 < m) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < n) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < n) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < n) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < n) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < n) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < n) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < n) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < n) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < n) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < n) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < n) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < n) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < n) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < n) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < n) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < n) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < n) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < n) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < n) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < n) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < n) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < n) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < n) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < n) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < n) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < n) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < n) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < n) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < n) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < n) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < n) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < n) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((0 < m) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((0 < m) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((0 < m) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((0 < m) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((0 < m) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((0 < m) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m n : ℕ} (hm : m > 0) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (0 < m) ↔ (m > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (0 < m) ↔ (m > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (0 < m) ↔ (m > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (0 < m) ↔ (m > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (0 < m) ↔ (m > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (0 < m) ↔ (m > 0) := by
  omega

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (0 < m) ↔ (m > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (0 < m) ↔ (m > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) ↔
    (∀ {m n : ℕ} (hm : m > 0) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) ↔
    (∀ {m n : ℕ} (hm : m > 0) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) ↔
    (∀ {m n : ℕ} (hm : m > 0) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) ↔
    (∀ {m n : ℕ} (hm : m > 0) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m n : ℕ} (hn : 0 < n) (hm : 0 < m), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) ↔
    (∀ {m n : ℕ} (hn : 0 < n) (hm : 0 < m), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) ↔
    (∀ {m n : ℕ} (hn : 0 < n) (hm : 0 < m), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) ↔
    (∀ {m n : ℕ} (hn : 0 < n) (hm : 0 < m), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) ↔
    (∀ {m n : ℕ} (hn : 0 < n) (hm : 0 < m), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m n : ℕ} (hm₀ : 0 < m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) ↔
    (∀ {m n : ℕ} (hm₀ : 0 < m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) ↔
    (∀ {m n : ℕ} (hm₀ : 0 < m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) ↔
    (∀ {m n : ℕ} (hm₀ : 0 < m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) ↔
    (∀ {m n : ℕ} (hm₀ : 0 < m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m n : ℕ} (hm : ¬(m ≤ 0)) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (0 < m) ↔ (¬(m ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (0 < m) ↔ (¬(m ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (0 < m) ↔ (¬(m ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (0 < m) ↔ (¬(m ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (0 < m) ↔ (¬(m ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (0 < m) ↔ (¬(m ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (0 < m) ↔ (¬(m ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (0 < m) ↔ (¬(m ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) ↔
    (∀ {m n : ℕ} (hm : ¬(m ≤ 0)) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) ↔
    (∀ {m n : ℕ} (hm : ¬(m ≤ 0)) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) ↔
    (∀ {m n : ℕ} (hm : ¬(m ≤ 0)) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) ↔
    (∀ {m n : ℕ} (hm : ¬(m ≤ 0)) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m n : ℕ} (hm : 1 ≤ m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (0 < m) ↔ (1 ≤ m) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (0 < m) ↔ (1 ≤ m) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (0 < m) ↔ (1 ≤ m) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (0 < m) ↔ (1 ≤ m) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (0 < m) ↔ (1 ≤ m) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (0 < m) ↔ (1 ≤ m) := by
  omega

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (0 < m) ↔ (1 ≤ m) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {m n : ℕ} :
    (0 < m) ↔ (1 ≤ m) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) ↔
    (∀ {m n : ℕ} (hm : 1 ≤ m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) ↔
    (∀ {m n : ℕ} (hm : 1 ≤ m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) ↔
    (∀ {m n : ℕ} (hm : 1 ≤ m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) ↔
    (∀ {m n : ℕ} (hm : 1 ≤ m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {m n : ℕ} (hm : 0 < m), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm : 0 < m), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) →
    (∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm : 0 < m), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) →
    (∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm : 0 < m), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) →
    (∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm : 0 < m), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) →
    (∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm : 0 < m), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) →
    (∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm : 0 < m), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) →
    (∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {m n : ℕ} (hm : 0 < m), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) →
    (∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n), Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hm : 0 < m) :
    (0 < n) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hm : 0 < m) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hm : 0 < m) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hm : 0 < m) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hm : 0 < m) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hm : 0 < m) :
    (0 < n) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hm : 0 < m) :
    (0 < n) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < m) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < m) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < m) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < m) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < m) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < m) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < m) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < m) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < m) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < m) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < m) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < m) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < m) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < m) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < m) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < m) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < m) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < m) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < m) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < m) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < m) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < m) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < m) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < m) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < m) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < m) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < m) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < m) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < m) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < m) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < m) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ), (0 < m) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
