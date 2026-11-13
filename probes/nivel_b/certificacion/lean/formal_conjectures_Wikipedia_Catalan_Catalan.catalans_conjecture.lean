import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Catalan's conjecture and related Diophantine equations

*References:*
- [Wikipedia - Catalan's conjecture](https://en.wikipedia.org/wiki/Catalan%27s_conjecture)
- [arXiv:2507.12397](https://arxiv.org/abs/2507.12397) (Lebesgue-Nagell equation)
-/

section

namespace Catalan

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b x y : ℕ) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < a) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < a) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < a) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < a) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < a) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < a) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < a) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((1 < a) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((1 < a) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((1 < a) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((1 < a) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((1 < a) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((1 < a) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b x y : ℕ) (ha : 1 ≤ a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 ≤ a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 ≤ a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 ≤ a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 ≤ a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 ≤ a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 ≤ a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 ≤ a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < a) ↔ (1 ≤ a) := by
  omega

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < a) ↔ (1 ≤ a) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < a) ↔ (1 ≤ a) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < a) ↔ (1 ≤ a) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < a) ↔ (1 ≤ a) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < a) ↔ (1 ≤ a) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < a) ↔ (1 ≤ a) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (1 ≤ a))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (1 ≤ a))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (1 ≤ a))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (1 ≤ a))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (1 ≤ a))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (1 ≤ a))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (1 ≤ a))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (1 ≤ a))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (1 ≤ a))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (1 ≤ a))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (1 ≤ a))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (1 ≤ a))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (1 ≤ a))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (1 ≤ a))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((1 < a) ↔ (1 ≤ a)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((1 < a) ↔ (1 ≤ a)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((1 < a) ↔ (1 ≤ a)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((1 < a) ↔ (1 ≤ a)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((1 < a) ↔ (1 ≤ a)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((1 < a) ↔ (1 ≤ a)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(2 : ℕ), (2 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(2 : ℕ), (2 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(2 : ℕ), (2 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(2 : ℕ), (1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (2 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(2 : ℕ), (2 : ℕ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(2 : ℕ), (2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(2 : ℕ), (2 : ℕ), (3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(2 : ℕ), (1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(2 : ℕ), (3 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (2 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(3 : ℕ), (2 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(2 : ℕ), (2 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(2 : ℕ), (2 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(2 : ℕ), (1 : ℕ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(2 : ℕ), (1 : ℕ), (3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(2 : ℕ), (3 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(2 : ℕ), (3 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (2 : ℕ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (2 : ℕ), (3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (3 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(3 : ℕ), (2 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(3 : ℕ), (2 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(3 : ℕ), (1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(2 : ℕ), (2 : ℕ), (3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b x y : ℕ) (ha : a > 1) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) :
    (1 < a) ↔ (a > 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) :
    (1 < a) ↔ (a > 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) :
    (1 < a) ↔ (a > 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) :
    (1 < a) ↔ (a > 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) :
    (1 < a) ↔ (a > 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) :
    (1 < a) ↔ (a > 1) := by
  omega

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) :
    (1 < a) ↔ (a > 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) :
    (1 < a) ↔ (a > 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔
    (∀ (a b x y : ℕ) (ha : a > 1) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔
    (∀ (a b x y : ℕ) (ha : a > 1) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔
    (∀ (a b x y : ℕ) (ha : a > 1) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔
    (∀ (a b x y : ℕ) (ha : a > 1) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b x y : ℕ) (hb : 1 < b) (ha : 1 < a) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔
    (∀ (a b x y : ℕ) (hb : 1 < b) (ha : 1 < a) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔
    (∀ (a b x y : ℕ) (hb : 1 < b) (ha : 1 < a) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔
    (∀ (a b x y : ℕ) (hb : 1 < b) (ha : 1 < a) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔
    (∀ (a b x y : ℕ) (hb : 1 < b) (ha : 1 < a) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b x y : ℕ) (ha₀ : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔
    (∀ (a b x y : ℕ) (ha₀ : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔
    (∀ (a b x y : ℕ) (ha₀ : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔
    (∀ (a b x y : ℕ) (ha₀ : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔
    (∀ (a b x y : ℕ) (ha₀ : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b x y : ℕ) (ha : ¬(a ≤ 1)) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) :
    (1 < a) ↔ (¬(a ≤ 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) :
    (1 < a) ↔ (¬(a ≤ 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) :
    (1 < a) ↔ (¬(a ≤ 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) :
    (1 < a) ↔ (¬(a ≤ 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) :
    (1 < a) ↔ (¬(a ≤ 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) :
    (1 < a) ↔ (¬(a ≤ 1)) := by
  omega

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) :
    (1 < a) ↔ (¬(a ≤ 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) :
    (1 < a) ↔ (¬(a ≤ 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔
    (∀ (a b x y : ℕ) (ha : ¬(a ≤ 1)) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔
    (∀ (a b x y : ℕ) (ha : ¬(a ≤ 1)) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔
    (∀ (a b x y : ℕ) (ha : ¬(a ≤ 1)) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔
    (∀ (a b x y : ℕ) (ha : ¬(a ≤ 1)) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b x y : ℕ) (ha : 2 ≤ a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) :
    (1 < a) ↔ (2 ≤ a) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) :
    (1 < a) ↔ (2 ≤ a) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) :
    (1 < a) ↔ (2 ≤ a) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) :
    (1 < a) ↔ (2 ≤ a) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) :
    (1 < a) ↔ (2 ≤ a) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) :
    (1 < a) ↔ (2 ≤ a) := by
  omega

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) :
    (1 < a) ↔ (2 ≤ a) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) :
    (1 < a) ↔ (2 ≤ a) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔
    (∀ (a b x y : ℕ) (ha : 2 ≤ a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔
    (∀ (a b x y : ℕ) (ha : 2 ≤ a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔
    (∀ (a b x y : ℕ) (ha : 2 ≤ a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔
    (∀ (a b x y : ℕ) (ha : 2 ≤ a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b x y : ℕ) (ha : a ≥ 1) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : a ≥ 1) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : a ≥ 1) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : a ≥ 1) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : a ≥ 1) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : a ≥ 1) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : a ≥ 1) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : a ≥ 1) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < a) ↔ (a ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < a) ↔ (a ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < a) ↔ (a ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < a) ↔ (a ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < a) ↔ (a ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < a) ↔ (a ≥ 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < a) ↔ (a ≥ 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (a ≥ 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (a ≥ 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (a ≥ 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (a ≥ 1))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (a ≥ 1))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (a ≥ 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (a ≥ 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (a ≥ 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (a ≥ 1))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (a ≥ 1))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (a ≥ 1))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (a ≥ 1))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (a ≥ 1))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (a ≥ 1))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (a ≥ 1))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (a ≥ 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (a ≥ 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (a ≥ 1))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (a ≥ 1))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (a ≥ 1))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (a ≥ 1))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (a ≥ 1))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (a ≥ 1))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (a ≥ 1))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (a ≥ 1))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (a ≥ 1))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (a ≥ 1))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (a ≥ 1))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (a ≥ 1))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (a ≥ 1))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (a ≥ 1))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (a ≥ 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((1 < a) ↔ (a ≥ 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((1 < a) ↔ (a ≥ 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((1 < a) ↔ (a ≥ 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((1 < a) ↔ (a ≥ 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((1 < a) ↔ (a ≥ 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((1 < a) ↔ (a ≥ 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b x y : ℕ) (ha : a > 1) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : a > 1) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : a > 1) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : a > 1) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : a > 1) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : a > 1) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : a > 1) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : a > 1) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : a > 1) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : a > 1) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : a > 1) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : a > 1) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : a > 1) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : a > 1) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : a > 1) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬(a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(2 : ℕ), (2 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(2 : ℕ), (2 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(2 : ℕ), (2 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(2 : ℕ), (1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (2 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(2 : ℕ), (2 : ℕ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(2 : ℕ), (2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(2 : ℕ), (2 : ℕ), (3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(2 : ℕ), (1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(2 : ℕ), (3 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (2 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(3 : ℕ), (2 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(2 : ℕ), (2 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(2 : ℕ), (2 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(2 : ℕ), (1 : ℕ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(2 : ℕ), (1 : ℕ), (3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(2 : ℕ), (3 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(2 : ℕ), (3 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (2 : ℕ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (2 : ℕ), (3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(1 : ℕ), (3 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(3 : ℕ), (2 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(3 : ℕ), (2 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(3 : ℕ), (1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), ¬((a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) ↔ (a = 3 ∧ b = 3 ∧ x = 3 ∧ y = 2)) :=
  ⟨(2 : ℕ), (2 : ℕ), (3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b x y : ℕ) (ha : 2 ≤ a) (hb : 1 ≤ b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 2 ≤ a) (hb : 1 ≤ b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 2 ≤ a) (hb : 1 ≤ b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 2 ≤ a) (hb : 1 ≤ b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 2 ≤ a) (hb : 1 ≤ b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 2 ≤ a) (hb : 1 ≤ b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 2 ≤ a) (hb : 1 ≤ b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 2 ≤ a) (hb : 1 ≤ b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (ha : 1 < a) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < b) ↔ (1 ≤ b) := by
  omega

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (ha : 1 < a) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < b) ↔ (1 ≤ b) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (ha : 1 < a) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < b) ↔ (1 ≤ b) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (ha : 1 < a) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < b) ↔ (1 ≤ b) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (ha : 1 < a) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < b) ↔ (1 ≤ b) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (ha : 1 < a) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < b) ↔ (1 ≤ b) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (ha : 1 < a) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < b) ↔ (1 ≤ b) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (1 ≤ b))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (1 ≤ b))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (1 ≤ b))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (1 ≤ b))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (1 ≤ b))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (1 ≤ b))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (1 ≤ b))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (1 ≤ b))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (1 ≤ b))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (1 ≤ b))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (1 ≤ b))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (1 ≤ b))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (1 ≤ b))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (1 ≤ b))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (1 ≤ b))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (1 ≤ b))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (1 ≤ b))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (1 ≤ b))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (1 ≤ b))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (1 ≤ b))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (1 ≤ b))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (1 ≤ b))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (1 ≤ b))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (1 ≤ b))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (1 ≤ b))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (1 ≤ b))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (1 ≤ b))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (1 ≤ b))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (1 ≤ b))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (1 ≤ b))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (1 ≤ b))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (1 ≤ b))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((1 < b) ↔ (1 ≤ b)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((1 < b) ↔ (1 ≤ b)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((1 < b) ↔ (1 ≤ b)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((1 < b) ↔ (1 ≤ b)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((1 < b) ↔ (1 ≤ b)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((1 < b) ↔ (1 ≤ b)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b x y : ℕ) (ha : 2 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 2 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 2 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 2 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 2 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 2 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 2 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 2 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < a) ↔ (2 < a) := by
  omega

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < a) ↔ (2 < a) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < a) ↔ (2 < a) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < a) ↔ (2 < a) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < a) ↔ (2 < a) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < a) ↔ (2 < a) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < a) ↔ (2 < a) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (2 < a))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (2 < a))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (2 < a))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (2 < a))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (2 < a))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (2 < a))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (2 < a))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (2 < a))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (2 < a))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (2 < a))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (2 < a))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (2 < a))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (2 < a))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (2 < a))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (2 < a))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (2 < a))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (2 < a))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (2 < a))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (2 < a))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (2 < a))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (2 < a))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (2 < a))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (2 < a))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (2 < a))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (2 < a))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (2 < a))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (2 < a))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (2 < a))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (2 < a))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (2 < a))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (2 < a))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (2 < a))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((1 < a) ↔ (2 < a)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((1 < a) ↔ (2 < a)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((1 < a) ↔ (2 < a)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((1 < a) ↔ (2 < a)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((1 < a) ↔ (2 < a)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((1 < a) ↔ (2 < a)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b x y : ℕ) (ha : 3 ≤ a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 3 ≤ a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 3 ≤ a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 3 ≤ a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 3 ≤ a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 3 ≤ a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 3 ≤ a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 3 ≤ a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < a) ↔ (3 ≤ a) := by
  omega

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < a) ↔ (3 ≤ a) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < a) ↔ (3 ≤ a) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < a) ↔ (3 ≤ a) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < a) ↔ (3 ≤ a) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < a) ↔ (3 ≤ a) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < a) ↔ (3 ≤ a) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (3 ≤ a))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (3 ≤ a))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (3 ≤ a))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (3 ≤ a))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (3 ≤ a))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (3 ≤ a))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (3 ≤ a))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (3 ≤ a))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (3 ≤ a))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (3 ≤ a))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (3 ≤ a))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (3 ≤ a))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (3 ≤ a))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (3 ≤ a))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (3 ≤ a))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (3 ≤ a))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (3 ≤ a))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (3 ≤ a))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (3 ≤ a))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (3 ≤ a))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (3 ≤ a))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (3 ≤ a))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (3 ≤ a))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (3 ≤ a))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (3 ≤ a))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (3 ≤ a))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (3 ≤ a))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (3 ≤ a))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (3 ≤ a))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (3 ≤ a))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (3 ≤ a))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < b) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < a) ↔ (3 ≤ a))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((1 < a) ↔ (3 ≤ a)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((1 < a) ↔ (3 ≤ a)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((1 < a) ↔ (3 ≤ a)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((1 < a) ↔ (3 ≤ a)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((1 < a) ↔ (3 ≤ a)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((1 < a) ↔ (3 ≤ a)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((1 < a) ↔ (3 ≤ a)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b x y : ℕ) (ha : 1 < a) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b x y : ℕ) (ha : 1 < a) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) →
    (∀ (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1), a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (ha : 1 < a) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < b) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (ha : 1 < a) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < b) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (ha : 1 < a) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < b) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (ha : 1 < a) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < b) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (ha : 1 < a) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < b) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (ha : 1 < a) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < b) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (ha : 1 < a) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    (1 < b) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ) (x : ℕ) (y : ℕ), (1 < a) ∧ (0 < x) ∧ (0 < y) ∧ (x ^ a - y ^ b = 1) ∧ (¬((1 < b) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((1 < b) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((1 < b) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((1 < b) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((1 < b) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((1 < b) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((1 < b) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b x y : ℕ) (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) (heq : x ^ a - y ^ b = 1) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
