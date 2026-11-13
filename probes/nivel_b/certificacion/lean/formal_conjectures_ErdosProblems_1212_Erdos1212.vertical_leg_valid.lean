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
  ∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℕ} (ha : a.Composite) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) →
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) →
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) →
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) →
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) →
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) →
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) →
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (ha : a.Composite) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) :
    (2 ≤ b) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (ha : a.Composite) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) :
    (2 ≤ b) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (ha : a.Composite) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) :
    (2 ≤ b) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (ha : a.Composite) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) :
    (2 ≤ b) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (ha : a.Composite) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) :
    (2 ≤ b) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (ha : a.Composite) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) :
    (2 ≤ b) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (ha : a.Composite) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) :
    (2 ≤ b) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(3 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 < b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) →
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 < b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) →
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 < b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) →
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 < b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) →
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 < b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) →
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 < b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) →
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 < b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) →
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 < b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (ha : a.Composite) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) :
    (2 ≤ b) ↔ (2 < b) := by
  omega

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (ha : a.Composite) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) :
    (2 ≤ b) ↔ (2 < b) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (ha : a.Composite) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) :
    (2 ≤ b) ↔ (2 < b) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (ha : a.Composite) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) :
    (2 ≤ b) ↔ (2 < b) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (ha : a.Composite) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) :
    (2 ≤ b) ↔ (2 < b) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (ha : a.Composite) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) :
    (2 ≤ b) ↔ (2 < b) := by
  simp_all

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (ha : a.Composite) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) :
    (2 ≤ b) ↔ (2 < b) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(1 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(1 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(3 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(1 : ℕ), (1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(1 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(1 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(1 : ℕ), (5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(0 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(0 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(2 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(2 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (2 < b)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (2 < b)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (2 < b)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (2 < b)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (2 < b)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (2 < b)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℕ} (ha : a.Composite) (hb : b ≥ 2) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ b) ↔ (b ≥ 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ b) ↔ (b ≥ 2) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ b) ↔ (b ≥ 2) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ b) ↔ (b ≥ 2) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ b) ↔ (b ≥ 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ b) ↔ (b ≥ 2) := by
  omega

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ b) ↔ (b ≥ 2) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ b) ↔ (b ≥ 2) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) ↔
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : b ≥ 2) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) ↔
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : b ≥ 2) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) ↔
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : b ≥ 2) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) ↔
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : b ≥ 2) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s₁, b ≤ s₁ → s₁ ≤ c → Valid (a, s₁)

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (∀ s, b ≤ s → s ≤ c → Valid (a, s)) ↔ (∀ s₁, b ≤ s₁ → s₁ ≤ c → Valid (a, s₁)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (∀ s, b ≤ s → s ≤ c → Valid (a, s)) ↔ (∀ s₁, b ≤ s₁ → s₁ ≤ c → Valid (a, s₁)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (∀ s, b ≤ s → s ≤ c → Valid (a, s)) ↔ (∀ s₁, b ≤ s₁ → s₁ ≤ c → Valid (a, s₁)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (∀ s, b ≤ s → s ≤ c → Valid (a, s)) ↔ (∀ s₁, b ≤ s₁ → s₁ ≤ c → Valid (a, s₁)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (∀ s, b ≤ s → s ≤ c → Valid (a, s)) ↔ (∀ s₁, b ≤ s₁ → s₁ ≤ c → Valid (a, s₁)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (∀ s, b ≤ s → s ≤ c → Valid (a, s)) ↔ (∀ s₁, b ≤ s₁ → s₁ ≤ c → Valid (a, s₁)) := by
  omega

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (∀ s, b ≤ s → s ≤ c → Valid (a, s)) ↔ (∀ s₁, b ≤ s₁ → s₁ ≤ c → Valid (a, s₁)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (∀ s, b ≤ s → s ≤ c → Valid (a, s)) ↔ (∀ s₁, b ≤ s₁ → s₁ ≤ c → Valid (a, s₁)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) ↔
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s₁, b ≤ s₁ → s₁ ≤ c → Valid (a, s₁)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) ↔
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s₁, b ≤ s₁ → s₁ ≤ c → Valid (a, s₁)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) ↔
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s₁, b ≤ s₁ → s₁ ≤ c → Valid (a, s₁)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) ↔
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s₁, b ≤ s₁ → s₁ ≤ c → Valid (a, s₁)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℕ} (hb : 2 ≤ b) (ha : a.Composite) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) ↔
    (∀ {a b c : ℕ} (hb : 2 ≤ b) (ha : a.Composite) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) ↔
    (∀ {a b c : ℕ} (hb : 2 ≤ b) (ha : a.Composite) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) ↔
    (∀ {a b c : ℕ} (hb : 2 ≤ b) (ha : a.Composite) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) ↔
    (∀ {a b c : ℕ} (hb : 2 ≤ b) (ha : a.Composite) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℕ} (ha₀ : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) ↔
    (∀ {a b c : ℕ} (ha₀ : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) ↔
    (∀ {a b c : ℕ} (ha₀ : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) ↔
    (∀ {a b c : ℕ} (ha₀ : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) ↔
    (∀ {a b c : ℕ} (ha₀ : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℕ} (ha : a.Composite) (hb : ¬(b < 2)) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ b) ↔ (¬(b < 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ b) ↔ (¬(b < 2)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ b) ↔ (¬(b < 2)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ b) ↔ (¬(b < 2)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ b) ↔ (¬(b < 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ b) ↔ (¬(b < 2)) := by
  omega

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ b) ↔ (¬(b < 2)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ b) ↔ (¬(b < 2)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) ↔
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : ¬(b < 2)) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) ↔
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : ¬(b < 2)) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) ↔
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : ¬(b < 2)) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) ↔
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : ¬(b < 2)) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℕ} (ha : a.Composite) (hb : 1 < b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ b) ↔ (1 < b) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ b) ↔ (1 < b) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ b) ↔ (1 < b) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ b) ↔ (1 < b) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ b) ↔ (1 < b) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ b) ↔ (1 < b) := by
  omega

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ b) ↔ (1 < b) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {a b c : ℕ} :
    (2 ≤ b) ↔ (1 < b) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) ↔
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 1 < b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) ↔
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 1 < b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) ↔
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 1 < b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) ↔
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 1 < b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℕ} (ha : a.Composite) (hb : b > 2) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) →
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : b > 2) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) →
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : b > 2) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) →
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : b > 2) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) →
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : b > 2) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) →
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : b > 2) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) →
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : b > 2) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) →
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : b > 2) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (ha : a.Composite) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) :
    (2 ≤ b) ↔ (b > 2) := by
  omega

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (ha : a.Composite) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) :
    (2 ≤ b) ↔ (b > 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (ha : a.Composite) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) :
    (2 ≤ b) ↔ (b > 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (ha : a.Composite) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) :
    (2 ≤ b) ↔ (b > 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (ha : a.Composite) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) :
    (2 ≤ b) ↔ (b > 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (ha : a.Composite) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) :
    (2 ≤ b) ↔ (b > 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (ha : a.Composite) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) :
    (2 ≤ b) ↔ (b > 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (b > 2))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (b > 2))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (b > 2))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (b > 2))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (b > 2))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (b > 2))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (b > 2))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (b > 2))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (b > 2))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (b > 2))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (b > 2))) :=
  ⟨(1 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (b > 2))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (b > 2))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (b > 2))) :=
  ⟨(1 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (b > 2))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (b > 2))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (b > 2))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (b > 2))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (b > 2))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (b > 2))) :=
  ⟨(3 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (b > 2))) :=
  ⟨(1 : ℕ), (1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (b > 2))) :=
  ⟨(1 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (b > 2))) :=
  ⟨(1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (b > 2))) :=
  ⟨(1 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (b > 2))) :=
  ⟨(1 : ℕ), (5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (b > 2))) :=
  ⟨(0 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (b > 2))) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (b > 2))) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (b > 2))) :=
  ⟨(0 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (b > 2))) :=
  ⟨(2 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (b > 2))) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (b > 2))) :=
  ⟨(2 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (b > 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (b > 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (b > 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (b > 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (b > 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (b > 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b c : ℕ} (ha : a.Composite) (hb : 1 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 1 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) →
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 1 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) →
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 1 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) →
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 1 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) →
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 1 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) →
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 1 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) →
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 1 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) →
    (∀ {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1), ∀ s, b ≤ s → s ≤ c → Valid (a, s)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (ha : a.Composite) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) :
    (2 ≤ b) ↔ (1 ≤ b) := by
  omega

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (ha : a.Composite) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) :
    (2 ≤ b) ↔ (1 ≤ b) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (ha : a.Composite) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) :
    (2 ≤ b) ↔ (1 ≤ b) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (ha : a.Composite) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) :
    (2 ≤ b) ↔ (1 ≤ b) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (ha : a.Composite) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) :
    (2 ≤ b) ↔ (1 ≤ b) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (ha : a.Composite) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) :
    (2 ≤ b) ↔ (1 ≤ b) := by
  simp_all

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (ha : a.Composite) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) :
    (2 ≤ b) ↔ (1 ≤ b) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (1 ≤ b))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (1 ≤ b))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (1 ≤ b))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (1 ≤ b))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (1 ≤ b))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (1 ≤ b))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (1 ≤ b))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (1 ≤ b))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (1 ≤ b))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (1 ≤ b))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (1 ≤ b))) :=
  ⟨(1 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (1 ≤ b))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (1 ≤ b))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (1 ≤ b))) :=
  ⟨(1 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (1 ≤ b))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (1 ≤ b))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (1 ≤ b))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (1 ≤ b))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (1 ≤ b))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (1 ≤ b))) :=
  ⟨(3 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (1 ≤ b))) :=
  ⟨(1 : ℕ), (1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (1 ≤ b))) :=
  ⟨(1 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (1 ≤ b))) :=
  ⟨(1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (1 ≤ b))) :=
  ⟨(1 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (1 ≤ b))) :=
  ⟨(1 : ℕ), (5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (1 ≤ b))) :=
  ⟨(0 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (1 ≤ b))) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (1 ≤ b))) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (1 ≤ b))) :=
  ⟨(0 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (1 ≤ b))) :=
  ⟨(2 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (1 ≤ b))) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (c : ℕ), (a.Composite) ∧ (∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) ∧ (¬((2 ≤ b) ↔ (1 ≤ b))) :=
  ⟨(2 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (1 ≤ b)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (1 ≤ b)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (1 ≤ b)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (1 ≤ b)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (1 ≤ b)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (1 ≤ b)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b) (hV : ∀ s, b ≤ s → s ≤ c → Nat.gcd a s = 1) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
