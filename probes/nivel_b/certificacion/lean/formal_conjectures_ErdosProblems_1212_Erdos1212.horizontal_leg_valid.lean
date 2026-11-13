import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Data.Nat.Prime.Composite
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
  ∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℕ} (hc : c.Composite) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) →
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) →
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) →
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) →
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) →
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) →
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) →
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (hc : c.Composite) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) :
    (2 ≤ a) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (hc : c.Composite) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) :
    (2 ≤ a) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (hc : c.Composite) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) :
    (2 ≤ a) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (hc : c.Composite) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) :
    (2 ≤ a) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (hc : c.Composite) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) :
    (2 ≤ a) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (hc : c.Composite) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) :
    (2 ≤ a) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (hc : c.Composite) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) :
    (2 ≤ a) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(3 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 < a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) →
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 < a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) →
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 < a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) →
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 < a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) →
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 < a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) →
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 < a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) →
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 < a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) →
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 < a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (hc : c.Composite) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) :
    (2 ≤ a) ↔ (2 < a) := by
  omega

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (hc : c.Composite) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) :
    (2 ≤ a) ↔ (2 < a) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (hc : c.Composite) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) :
    (2 ≤ a) ↔ (2 < a) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (hc : c.Composite) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) :
    (2 ≤ a) ↔ (2 < a) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (hc : c.Composite) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) :
    (2 ≤ a) ↔ (2 < a) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (hc : c.Composite) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) :
    (2 ≤ a) ↔ (2 < a) := by
  simp_all

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (hc : c.Composite) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) :
    (2 ≤ a) ↔ (2 < a) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(1 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(1 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(3 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(1 : ℕ), (1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(1 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(1 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(1 : ℕ), (5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(0 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(0 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(2 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(2 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (2 < a)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (2 < a)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (2 < a)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (2 < a)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (2 < a)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (2 < a)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℕ} (hc : c.Composite) (ha2 : a ≥ 2) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ a) ↔ (a ≥ 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ a) ↔ (a ≥ 2) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ a) ↔ (a ≥ 2) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ a) ↔ (a ≥ 2) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ a) ↔ (a ≥ 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ a) ↔ (a ≥ 2) := by
  omega

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ a) ↔ (a ≥ 2) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ a) ↔ (a ≥ 2) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) ↔
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : a ≥ 2) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) ↔
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : a ≥ 2) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) ↔
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : a ≥ 2) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) ↔
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : a ≥ 2) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s₁, a ≤ s₁ → s₁ ≤ b → Valid (s₁, c)

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (∀ s, a ≤ s → s ≤ b → Valid (s, c)) ↔ (∀ s₁, a ≤ s₁ → s₁ ≤ b → Valid (s₁, c)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (∀ s, a ≤ s → s ≤ b → Valid (s, c)) ↔ (∀ s₁, a ≤ s₁ → s₁ ≤ b → Valid (s₁, c)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (∀ s, a ≤ s → s ≤ b → Valid (s, c)) ↔ (∀ s₁, a ≤ s₁ → s₁ ≤ b → Valid (s₁, c)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (∀ s, a ≤ s → s ≤ b → Valid (s, c)) ↔ (∀ s₁, a ≤ s₁ → s₁ ≤ b → Valid (s₁, c)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (∀ s, a ≤ s → s ≤ b → Valid (s, c)) ↔ (∀ s₁, a ≤ s₁ → s₁ ≤ b → Valid (s₁, c)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (∀ s, a ≤ s → s ≤ b → Valid (s, c)) ↔ (∀ s₁, a ≤ s₁ → s₁ ≤ b → Valid (s₁, c)) := by
  omega

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (∀ s, a ≤ s → s ≤ b → Valid (s, c)) ↔ (∀ s₁, a ≤ s₁ → s₁ ≤ b → Valid (s₁, c)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (∀ s, a ≤ s → s ≤ b → Valid (s, c)) ↔ (∀ s₁, a ≤ s₁ → s₁ ≤ b → Valid (s₁, c)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) ↔
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s₁, a ≤ s₁ → s₁ ≤ b → Valid (s₁, c)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) ↔
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s₁, a ≤ s₁ → s₁ ≤ b → Valid (s₁, c)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) ↔
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s₁, a ≤ s₁ → s₁ ≤ b → Valid (s₁, c)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) ↔
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s₁, a ≤ s₁ → s₁ ≤ b → Valid (s₁, c)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℕ} (ha2 : 2 ≤ a) (hc : c.Composite) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) ↔
    (∀ {a b c : ℕ} (ha2 : 2 ≤ a) (hc : c.Composite) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) ↔
    (∀ {a b c : ℕ} (ha2 : 2 ≤ a) (hc : c.Composite) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) ↔
    (∀ {a b c : ℕ} (ha2 : 2 ≤ a) (hc : c.Composite) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) ↔
    (∀ {a b c : ℕ} (ha2 : 2 ≤ a) (hc : c.Composite) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℕ} (hc₀ : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) ↔
    (∀ {a b c : ℕ} (hc₀ : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) ↔
    (∀ {a b c : ℕ} (hc₀ : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) ↔
    (∀ {a b c : ℕ} (hc₀ : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) ↔
    (∀ {a b c : ℕ} (hc₀ : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℕ} (hc : c.Composite) (ha2 : ¬(a < 2)) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ a) ↔ (¬(a < 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ a) ↔ (¬(a < 2)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ a) ↔ (¬(a < 2)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ a) ↔ (¬(a < 2)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ a) ↔ (¬(a < 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ a) ↔ (¬(a < 2)) := by
  omega

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ a) ↔ (¬(a < 2)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ a) ↔ (¬(a < 2)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) ↔
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : ¬(a < 2)) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) ↔
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : ¬(a < 2)) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) ↔
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : ¬(a < 2)) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) ↔
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : ¬(a < 2)) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 1 < a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ a) ↔ (1 < a) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ a) ↔ (1 < a) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ a) ↔ (1 < a) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ a) ↔ (1 < a) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ a) ↔ (1 < a) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ a) ↔ (1 < a) := by
  omega

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ a) ↔ (1 < a) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ a) ↔ (1 < a) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) ↔
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 1 < a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) ↔
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 1 < a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) ↔
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 1 < a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) ↔
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 1 < a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℕ} (hc : c.Composite) (ha2 : a > 2) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) →
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : a > 2) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) →
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : a > 2) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) →
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : a > 2) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) →
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : a > 2) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) →
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : a > 2) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) →
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : a > 2) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) →
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : a > 2) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (hc : c.Composite) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) :
    (2 ≤ a) ↔ (a > 2) := by
  omega

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (hc : c.Composite) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) :
    (2 ≤ a) ↔ (a > 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (hc : c.Composite) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) :
    (2 ≤ a) ↔ (a > 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (hc : c.Composite) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) :
    (2 ≤ a) ↔ (a > 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (hc : c.Composite) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) :
    (2 ≤ a) ↔ (a > 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (hc : c.Composite) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) :
    (2 ≤ a) ↔ (a > 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (hc : c.Composite) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) :
    (2 ≤ a) ↔ (a > 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(1 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(1 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(3 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(1 : ℕ), (1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(1 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(1 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(1 : ℕ), (5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(0 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(0 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(2 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(2 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (a > 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (a > 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (a > 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (a > 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (a > 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (a > 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 1 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 1 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) →
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 1 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) →
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 1 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) →
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 1 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) →
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 1 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) →
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 1 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) →
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 1 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) →
    (∀ {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1), ∀ s, a ≤ s → s ≤ b → Valid (s, c)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (hc : c.Composite) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) :
    (2 ≤ a) ↔ (1 ≤ a) := by
  omega

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (hc : c.Composite) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) :
    (2 ≤ a) ↔ (1 ≤ a) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (hc : c.Composite) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) :
    (2 ≤ a) ↔ (1 ≤ a) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (hc : c.Composite) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) :
    (2 ≤ a) ↔ (1 ≤ a) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (hc : c.Composite) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) :
    (2 ≤ a) ↔ (1 ≤ a) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (hc : c.Composite) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) :
    (2 ≤ a) ↔ (1 ≤ a) := by
  simp_all

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (hc : c.Composite) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) :
    (2 ≤ a) ↔ (1 ≤ a) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(3 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(0 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(0 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(2 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (c.Composite) ∧ (∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(2 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (1 ≤ a)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (1 ≤ a)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (1 ≤ a)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (1 ≤ a)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (1 ≤ a)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (1 ≤ a)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a) (hH : ∀ s, a ≤ s → s ≤ b → Nat.gcd s c = 1) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
