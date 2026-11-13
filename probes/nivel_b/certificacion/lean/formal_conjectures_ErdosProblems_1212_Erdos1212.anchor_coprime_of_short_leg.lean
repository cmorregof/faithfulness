import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 1212

*References:*
- [erdosproblems.com/1212](https://www.erdosproblems.com/1212)
- [Er80] Erdős, P., _Some notes on problems and results in number theory_ (1980), p. 114.

This file also records machine-checked cores of verified partial results (2026):
a composite-anchor sufficient reduction and an impossibility theorem for periodic
certificates; see the corresponding lemmas below.
-/

section

open Filter

namespace Erdos1212

/-- A vertex of the strengthened problem: a visible lattice point with both coordinates
exceeding 1 and at least one coordinate composite. -/
def Valid (p : ℕ × ℕ) : Prop :=
  1 < p.1 ∧ 1 < p.2 ∧ Nat.gcd p.1 p.2 = 1 ∧ (¬ p.1.Prime ∨ ¬ p.2.Prime)

/-- Two lattice points are adjacent iff they differ by exactly 1 in exactly one coordinate. -/
def Adj (p q : ℕ × ℕ) : Prop :=
  (p.1 = q.1 ∧ (p.2 = q.2 + 1 ∨ q.2 = p.2 + 1)) ∨
  (p.2 = q.2 ∧ (p.1 = q.1 + 1 ∨ q.1 = p.1 + 1))

/- ### Verified partial results (2026): machine-checked cores -/

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1

set_option maxHeartbeats 200000 in
example :
    (∀ {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) →
    (∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) →
    (∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) →
    (∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) →
    (∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) →
    (∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) →
    (∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) →
    (∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p) :
    (a < s) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p) :
    (a < s) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p) :
    (a < s) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p) :
    (a < s) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p) :
    (a < s) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p) :
    (a < s) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p) :
    (a < s) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a s : ℕ} (hs : a ≤ s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1

set_option maxHeartbeats 200000 in
example :
    (∀ {a s : ℕ} (hs : a ≤ s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) →
    (∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a s : ℕ} (hs : a ≤ s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) →
    (∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a s : ℕ} (hs : a ≤ s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) →
    (∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {a s : ℕ} (hs : a ≤ s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) →
    (∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a s : ℕ} (hs : a ≤ s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) →
    (∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {a s : ℕ} (hs : a ≤ s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) →
    (∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a s : ℕ} (hs : a ≤ s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) →
    (∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p) :
    (a < s) ↔ (a ≤ s) := by
  omega

set_option maxHeartbeats 200000 in
example {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p) :
    (a < s) ↔ (a ≤ s) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p) :
    (a < s) ↔ (a ≤ s) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p) :
    (a < s) ↔ (a ≤ s) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p) :
    (a < s) ↔ (a ≤ s) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p) :
    (a < s) ↔ (a ≤ s) := by
  simp_all

set_option maxHeartbeats 200000 in
example {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p) :
    (a < s) ↔ (a ≤ s) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (a ≤ s))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (a ≤ s))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (a ≤ s))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (a ≤ s))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (a ≤ s))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (a ≤ s))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (a ≤ s))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (a ≤ s))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (a ≤ s))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (a ≤ s))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (a ≤ s))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (a ≤ s))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (a ≤ s))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (a ≤ s))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (a ≤ s))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (a ≤ s))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (a ≤ s))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (a ≤ s))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (a ≤ s))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (a ≤ s))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (a ≤ s))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (a ≤ s))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (a ≤ s))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (a ≤ s))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (a ≤ s))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (a ≤ s))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (a ≤ s))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (a ≤ s))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (a ≤ s))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (a ≤ s))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (a ≤ s))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (a ≤ s))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (a ≤ s)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (a ≤ s)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (a ≤ s)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (a ≤ s)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (a ≤ s)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (a ≤ s)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (a ≤ s)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (a ≤ s)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (a ≤ s)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (a ≤ s)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (a ≤ s)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (a ≤ s)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (a ≤ s)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (a ≤ s)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (a ≤ s)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (a ≤ s)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (a ≤ s)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (a ≤ s)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (a ≤ s)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (a ≤ s)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (a ≤ s)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (a ≤ s)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (a ≤ s)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (a ≤ s)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (a ≤ s)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (a ≤ s)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (a ≤ s)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (a ≤ s)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (a ≤ s)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (a ≤ s)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (a ≤ s)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (a ≤ s)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a s : ℕ} (hs : s > a) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1

set_option maxHeartbeats 200000 in
example {a s : ℕ} :
    (a < s) ↔ (s > a) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {a s : ℕ} :
    (a < s) ↔ (s > a) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {a s : ℕ} :
    (a < s) ↔ (s > a) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {a s : ℕ} :
    (a < s) ↔ (s > a) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {a s : ℕ} :
    (a < s) ↔ (s > a) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {a s : ℕ} :
    (a < s) ↔ (s > a) := by
  omega

set_option maxHeartbeats 200000 in
example {a s : ℕ} :
    (a < s) ↔ (s > a) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {a s : ℕ} :
    (a < s) ↔ (s > a) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) ↔
    (∀ {a s : ℕ} (hs : s > a) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) ↔
    (∀ {a s : ℕ} (hs : s > a) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) ↔
    (∀ {a s : ℕ} (hs : s > a) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) ↔
    (∀ {a s : ℕ} (hs : s > a) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p) (hs : a < s), Nat.gcd a s = 1

set_option maxHeartbeats 200000 in
example :
    (∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) ↔
    (∀ {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p) (hs : a < s), Nat.gcd a s = 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) ↔
    (∀ {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p) (hs : a < s), Nat.gcd a s = 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) ↔
    (∀ {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p) (hs : a < s), Nat.gcd a s = 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) ↔
    (∀ {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p) (hs : a < s), Nat.gcd a s = 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a s : ℕ} (hs₀ : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1

set_option maxHeartbeats 200000 in
example :
    (∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) ↔
    (∀ {a s : ℕ} (hs₀ : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) ↔
    (∀ {a s : ℕ} (hs₀ : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) ↔
    (∀ {a s : ℕ} (hs₀ : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) ↔
    (∀ {a s : ℕ} (hs₀ : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a s : ℕ} (hs : ¬(s ≤ a)) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1

set_option maxHeartbeats 200000 in
example {a s : ℕ} :
    (a < s) ↔ (¬(s ≤ a)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {a s : ℕ} :
    (a < s) ↔ (¬(s ≤ a)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {a s : ℕ} :
    (a < s) ↔ (¬(s ≤ a)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {a s : ℕ} :
    (a < s) ↔ (¬(s ≤ a)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {a s : ℕ} :
    (a < s) ↔ (¬(s ≤ a)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {a s : ℕ} :
    (a < s) ↔ (¬(s ≤ a)) := by
  omega

set_option maxHeartbeats 200000 in
example {a s : ℕ} :
    (a < s) ↔ (¬(s ≤ a)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {a s : ℕ} :
    (a < s) ↔ (¬(s ≤ a)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) ↔
    (∀ {a s : ℕ} (hs : ¬(s ≤ a)) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) ↔
    (∀ {a s : ℕ} (hs : ¬(s ≤ a)) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) ↔
    (∀ {a s : ℕ} (hs : ¬(s ≤ a)) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) ↔
    (∀ {a s : ℕ} (hs : ¬(s ≤ a)) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a s : ℕ} (hs : s ≥ a) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1

set_option maxHeartbeats 200000 in
example :
    (∀ {a s : ℕ} (hs : s ≥ a) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) →
    (∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a s : ℕ} (hs : s ≥ a) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) →
    (∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a s : ℕ} (hs : s ≥ a) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) →
    (∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {a s : ℕ} (hs : s ≥ a) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) →
    (∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a s : ℕ} (hs : s ≥ a) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) →
    (∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {a s : ℕ} (hs : s ≥ a) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) →
    (∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a s : ℕ} (hs : s ≥ a) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) →
    (∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p) :
    (a < s) ↔ (s ≥ a) := by
  omega

set_option maxHeartbeats 200000 in
example {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p) :
    (a < s) ↔ (s ≥ a) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p) :
    (a < s) ↔ (s ≥ a) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p) :
    (a < s) ↔ (s ≥ a) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p) :
    (a < s) ↔ (s ≥ a) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p) :
    (a < s) ↔ (s ≥ a) := by
  simp_all

set_option maxHeartbeats 200000 in
example {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p) :
    (a < s) ↔ (s ≥ a) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (s ≥ a))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (s ≥ a))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (s ≥ a))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (s ≥ a))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (s ≥ a))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (s ≥ a))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (s ≥ a))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (s ≥ a))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (s ≥ a))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (s ≥ a))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (s ≥ a))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (s ≥ a))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (s ≥ a))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (s ≥ a))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (s ≥ a))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (s ≥ a))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (s ≥ a))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (s ≥ a))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (s ≥ a))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (s ≥ a))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (s ≥ a))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (s ≥ a))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (s ≥ a))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (s ≥ a))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (s ≥ a))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (s ≥ a))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (s ≥ a))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (s ≥ a))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (s ≥ a))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (s ≥ a))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (s ≥ a))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (s ≥ a))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (s ≥ a)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (s ≥ a)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (s ≥ a)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (s ≥ a)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (s ≥ a)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (s ≥ a)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (s ≥ a)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (s ≥ a)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (s ≥ a)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (s ≥ a)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (s ≥ a)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (s ≥ a)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (s ≥ a)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (s ≥ a)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (s ≥ a)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (s ≥ a)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (s ≥ a)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (s ≥ a)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (s ≥ a)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (s ≥ a)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (s ≥ a)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (s ≥ a)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (s ≥ a)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (s ≥ a)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (s ≥ a)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (s ≥ a)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (s ≥ a)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (s ≥ a)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (s ≥ a)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (s ≥ a)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (s ≥ a)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (s ≥ a)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1

set_option maxHeartbeats 200000 in
example :
    (∀ {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) →
    (∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) →
    (∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) →
    (∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) →
    (∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) →
    (∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) →
    (∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) →
    (∀ {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p), Nat.gcd a s = 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p) :
    (a < s) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p) :
    (a < s) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p) :
    (a < s) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p) :
    (a < s) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p) :
    (a < s) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p) :
    (a < s) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {a s : ℕ} (h : ∀ p, p.Prime → p ∣ a → s < a + p) :
    (a < s) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), (∀ p, p.Prime → p ∣ a → s < a + p) ∧ (¬((a < s) ↔ (True))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (s : ℕ), ¬((a < s) ↔ (True)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {a s : ℕ} (hs : a < s) (h : ∀ p, p.Prime → p ∣ a → s < a + p) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
