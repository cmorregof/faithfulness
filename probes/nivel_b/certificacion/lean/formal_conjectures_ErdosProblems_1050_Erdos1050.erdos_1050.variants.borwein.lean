import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 1050

*References:* 
- [erdosproblems.com/1050](https://www.erdosproblems.com/1050)
- [Bo91] Borwein, Peter B., On the irrationality of {$\sum(1/(q^n+r))$}. J. Number Theory (1991), 253--259.
- [Bo92] Borwein, Peter B., On the irrationality of certain series. Math. Proc. Camb. Phil. Soc. (1992), 141--146.
- [Er48] Erdős, P., On arithmetical properties of Lambert series. J. Indian Math. Soc. (N.S.) (1948), 63-66.
- [Er88c] Erdős, P., On the irrationality of certain series: problems and results. New advances in transcendence theory (Durham, 1986) (1988), 102-109.

Is $\sum_{n=1}^\infty \frac{1}{2^n - 3}$ irrational?

The answer is **yes**, proved by P. B. Borwein [Bo91] (with a cleaner self-contained proof in [Bo92]),
specialized to $q = 2$, $r = -3$.

A formal Lean proof is given in an external repository,
[`gotrevor/lean-gallery`](https://github.com/gotrevor/lean-gallery), formalized by Trevor Morris with
Claude Code and Harmonic's Aristotle.
-/

section

namespace Erdos1050

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(0 : ℤ), (0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(0 : ℤ), (-1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(-1 : ℤ), (0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(0 : ℤ), (1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(-1 : ℤ), (-1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(1 : ℤ), (0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(0 : ℤ), (2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(-1 : ℤ), (1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(1 : ℤ), (-1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(2 : ℤ), (0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(0 : ℤ), (3 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(-1 : ℤ), (2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(1 : ℤ), (1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(2 : ℤ), (-1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(3 : ℤ), (0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(0 : ℤ), (1/2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(-1 : ℤ), (3 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(1 : ℤ), (2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(2 : ℤ), (1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(3 : ℤ), (-1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(-2 : ℤ), (0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(-1 : ℤ), (1/2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(1 : ℤ), (3 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(2 : ℤ), (2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(3 : ℤ), (1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(-2 : ℤ), (-1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(1 : ℤ), (1/2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(2 : ℤ), (3 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(3 : ℤ), (2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(-2 : ℤ), (1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(2 : ℤ), (1/2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(3 : ℤ), (3 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ), ¬((2 ≤ q) ↔ (True)) :=
  ⟨(2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ), ¬((2 ≤ q) ↔ (True)) :=
  ⟨(1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ), ¬((2 ≤ q) ↔ (True)) :=
  ⟨(3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ), ¬((2 ≤ q) ↔ (True)) :=
  ⟨(0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ), ¬((2 ≤ q) ↔ (True)) :=
  ⟨(-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ), ¬((2 ≤ q) ↔ (True)) :=
  ⟨(-2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℤ) (hq : 2 < q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : 2 < q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : 2 < q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : 2 < q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : 2 < q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : 2 < q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : 2 < q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : 2 < q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (2 < q) := by
  omega

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (2 < q) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (2 < q) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (2 < q) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (2 < q) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (2 < q) := by
  simp_all

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (2 < q) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (2 < q))) :=
  ⟨(0 : ℤ), (0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (2 < q))) :=
  ⟨(0 : ℤ), (-1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (2 < q))) :=
  ⟨(-1 : ℤ), (0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (2 < q))) :=
  ⟨(0 : ℤ), (1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (2 < q))) :=
  ⟨(-1 : ℤ), (-1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (2 < q))) :=
  ⟨(1 : ℤ), (0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (2 < q))) :=
  ⟨(0 : ℤ), (2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (2 < q))) :=
  ⟨(-1 : ℤ), (1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (2 < q))) :=
  ⟨(1 : ℤ), (-1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (2 < q))) :=
  ⟨(2 : ℤ), (0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (2 < q))) :=
  ⟨(0 : ℤ), (3 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (2 < q))) :=
  ⟨(-1 : ℤ), (2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (2 < q))) :=
  ⟨(1 : ℤ), (1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (2 < q))) :=
  ⟨(2 : ℤ), (-1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (2 < q))) :=
  ⟨(3 : ℤ), (0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (2 < q))) :=
  ⟨(0 : ℤ), (1/2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (2 < q))) :=
  ⟨(-1 : ℤ), (3 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (2 < q))) :=
  ⟨(1 : ℤ), (2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (2 < q))) :=
  ⟨(2 : ℤ), (1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (2 < q))) :=
  ⟨(3 : ℤ), (-1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (2 < q))) :=
  ⟨(-2 : ℤ), (0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (2 < q))) :=
  ⟨(-1 : ℤ), (1/2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (2 < q))) :=
  ⟨(1 : ℤ), (3 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (2 < q))) :=
  ⟨(2 : ℤ), (2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (2 < q))) :=
  ⟨(3 : ℤ), (1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (2 < q))) :=
  ⟨(-2 : ℤ), (-1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (2 < q))) :=
  ⟨(1 : ℤ), (1/2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (2 < q))) :=
  ⟨(2 : ℤ), (3 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (2 < q))) :=
  ⟨(3 : ℤ), (2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (2 < q))) :=
  ⟨(-2 : ℤ), (1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (2 < q))) :=
  ⟨(2 : ℤ), (1/2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (2 < q))) :=
  ⟨(3 : ℤ), (3 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ), ¬((2 ≤ q) ↔ (2 < q)) :=
  ⟨(2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ), ¬((2 ≤ q) ↔ (2 < q)) :=
  ⟨(1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ), ¬((2 ≤ q) ↔ (2 < q)) :=
  ⟨(3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ), ¬((2 ≤ q) ↔ (2 < q)) :=
  ⟨(0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ), ¬((2 ≤ q) ↔ (2 < q)) :=
  ⟨(-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ), ¬((2 ≤ q) ↔ (2 < q)) :=
  ⟨(-2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℤ) (hq : 3 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : 3 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : 3 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : 3 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : 3 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : 3 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : 3 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : 3 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (3 ≤ q) := by
  omega

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (3 ≤ q) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (3 ≤ q) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (3 ≤ q) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (3 ≤ q) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (3 ≤ q) := by
  simp_all

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (3 ≤ q) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (3 ≤ q))) :=
  ⟨(0 : ℤ), (0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (3 ≤ q))) :=
  ⟨(0 : ℤ), (-1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (3 ≤ q))) :=
  ⟨(-1 : ℤ), (0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (3 ≤ q))) :=
  ⟨(0 : ℤ), (1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (3 ≤ q))) :=
  ⟨(-1 : ℤ), (-1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (3 ≤ q))) :=
  ⟨(1 : ℤ), (0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (3 ≤ q))) :=
  ⟨(0 : ℤ), (2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (3 ≤ q))) :=
  ⟨(-1 : ℤ), (1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (3 ≤ q))) :=
  ⟨(1 : ℤ), (-1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (3 ≤ q))) :=
  ⟨(2 : ℤ), (0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (3 ≤ q))) :=
  ⟨(0 : ℤ), (3 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (3 ≤ q))) :=
  ⟨(-1 : ℤ), (2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (3 ≤ q))) :=
  ⟨(1 : ℤ), (1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (3 ≤ q))) :=
  ⟨(2 : ℤ), (-1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (3 ≤ q))) :=
  ⟨(3 : ℤ), (0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (3 ≤ q))) :=
  ⟨(0 : ℤ), (4 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (3 ≤ q))) :=
  ⟨(-1 : ℤ), (3 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (3 ≤ q))) :=
  ⟨(1 : ℤ), (2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (3 ≤ q))) :=
  ⟨(2 : ℤ), (1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (3 ≤ q))) :=
  ⟨(3 : ℤ), (-1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (3 ≤ q))) :=
  ⟨(4 : ℤ), (0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (3 ≤ q))) :=
  ⟨(0 : ℤ), (1/2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (3 ≤ q))) :=
  ⟨(-1 : ℤ), (4 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (3 ≤ q))) :=
  ⟨(1 : ℤ), (3 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (3 ≤ q))) :=
  ⟨(2 : ℤ), (2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (3 ≤ q))) :=
  ⟨(3 : ℤ), (1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (3 ≤ q))) :=
  ⟨(4 : ℤ), (-1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (3 ≤ q))) :=
  ⟨(-2 : ℤ), (0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (3 ≤ q))) :=
  ⟨(-1 : ℤ), (1/2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (3 ≤ q))) :=
  ⟨(1 : ℤ), (4 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (3 ≤ q))) :=
  ⟨(2 : ℤ), (3 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (3 ≤ q))) :=
  ⟨(3 : ℤ), (2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ), ¬((2 ≤ q) ↔ (3 ≤ q)) :=
  ⟨(2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ), ¬((2 ≤ q) ↔ (3 ≤ q)) :=
  ⟨(1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ), ¬((2 ≤ q) ↔ (3 ≤ q)) :=
  ⟨(3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ), ¬((2 ≤ q) ↔ (3 ≤ q)) :=
  ⟨(4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ), ¬((2 ≤ q) ↔ (3 ≤ q)) :=
  ⟨(0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ), ¬((2 ≤ q) ↔ (3 ≤ q)) :=
  ⟨(-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ), ¬((2 ≤ q) ↔ (3 ≤ q)) :=
  ⟨(-2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℤ) (hq : q ≥ 2) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) :
    (2 ≤ q) ↔ (q ≥ 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) :
    (2 ≤ q) ↔ (q ≥ 2) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) :
    (2 ≤ q) ↔ (q ≥ 2) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) :
    (2 ≤ q) ↔ (q ≥ 2) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) :
    (2 ≤ q) ↔ (q ≥ 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) :
    (2 ≤ q) ↔ (q ≥ 2) := by
  omega

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) :
    (2 ≤ q) ↔ (q ≥ 2) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) :
    (2 ≤ q) ↔ (q ≥ 2) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) ↔
    (∀ (q : ℤ) (hq : q ≥ 2) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) ↔
    (∀ (q : ℤ) (hq : q ≥ 2) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) ↔
    (∀ (q : ℤ) (hq : q ≥ 2) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) ↔
    (∀ (q : ℤ) (hq : q ≥ 2) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : ¬(r = 0)) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) :
    (r ≠ 0) ↔ (¬(r = 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) :
    (r ≠ 0) ↔ (¬(r = 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) :
    (r ≠ 0) ↔ (¬(r = 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) :
    (r ≠ 0) ↔ (¬(r = 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) :
    (r ≠ 0) ↔ (¬(r = 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) :
    (r ≠ 0) ↔ (¬(r = 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) :
    (r ≠ 0) ↔ (¬(r = 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) :
    (r ≠ 0) ↔ (¬(r = 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) ↔
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : ¬(r = 0)) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) ↔
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : ¬(r = 0)) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) ↔
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : ¬(r = 0)) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) ↔
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : ¬(r = 0)) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) (hr : r ≠ 0), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) ↔
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) (hr : r ≠ 0), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) ↔
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) (hr : r ≠ 0), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) ↔
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) (hr : r ≠ 0), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) ↔
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) (hr : r ≠ 0), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℤ) (hq₀ : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) ↔
    (∀ (q : ℤ) (hq₀ : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) ↔
    (∀ (q : ℤ) (hq₀ : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) ↔
    (∀ (q : ℤ) (hq₀ : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) ↔
    (∀ (q : ℤ) (hq₀ : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℤ) (hq : ¬(q < 2)) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) :
    (2 ≤ q) ↔ (¬(q < 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) :
    (2 ≤ q) ↔ (¬(q < 2)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) :
    (2 ≤ q) ↔ (¬(q < 2)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) :
    (2 ≤ q) ↔ (¬(q < 2)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) :
    (2 ≤ q) ↔ (¬(q < 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) :
    (2 ≤ q) ↔ (¬(q < 2)) := by
  omega

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) :
    (2 ≤ q) ↔ (¬(q < 2)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) :
    (2 ≤ q) ↔ (¬(q < 2)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) ↔
    (∀ (q : ℤ) (hq : ¬(q < 2)) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) ↔
    (∀ (q : ℤ) (hq : ¬(q < 2)) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) ↔
    (∀ (q : ℤ) (hq : ¬(q < 2)) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) ↔
    (∀ (q : ℤ) (hq : ¬(q < 2)) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℤ) (hq : 1 < q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) :
    (2 ≤ q) ↔ (1 < q) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) :
    (2 ≤ q) ↔ (1 < q) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) :
    (2 ≤ q) ↔ (1 < q) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) :
    (2 ≤ q) ↔ (1 < q) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) :
    (2 ≤ q) ↔ (1 < q) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) :
    (2 ≤ q) ↔ (1 < q) := by
  omega

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) :
    (2 ≤ q) ↔ (1 < q) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) :
    (2 ≤ q) ↔ (1 < q) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) ↔
    (∀ (q : ℤ) (hq : 1 < q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) ↔
    (∀ (q : ℤ) (hq : 1 < q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) ↔
    (∀ (q : ℤ) (hq : 1 < q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) ↔
    (∀ (q : ℤ) (hq : 1 < q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℤ) (hq : q > 2) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : q > 2) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : q > 2) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : q > 2) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : q > 2) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : q > 2) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : q > 2) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : q > 2) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (q > 2) := by
  omega

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (q > 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (q > 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (q > 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (q > 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (q > 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (q > 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q > 2))) :=
  ⟨(0 : ℤ), (0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q > 2))) :=
  ⟨(0 : ℤ), (-1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q > 2))) :=
  ⟨(-1 : ℤ), (0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q > 2))) :=
  ⟨(0 : ℤ), (1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q > 2))) :=
  ⟨(-1 : ℤ), (-1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q > 2))) :=
  ⟨(1 : ℤ), (0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q > 2))) :=
  ⟨(0 : ℤ), (2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q > 2))) :=
  ⟨(-1 : ℤ), (1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q > 2))) :=
  ⟨(1 : ℤ), (-1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q > 2))) :=
  ⟨(2 : ℤ), (0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q > 2))) :=
  ⟨(0 : ℤ), (3 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q > 2))) :=
  ⟨(-1 : ℤ), (2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q > 2))) :=
  ⟨(1 : ℤ), (1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q > 2))) :=
  ⟨(2 : ℤ), (-1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q > 2))) :=
  ⟨(3 : ℤ), (0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q > 2))) :=
  ⟨(0 : ℤ), (1/2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q > 2))) :=
  ⟨(-1 : ℤ), (3 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q > 2))) :=
  ⟨(1 : ℤ), (2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q > 2))) :=
  ⟨(2 : ℤ), (1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q > 2))) :=
  ⟨(3 : ℤ), (-1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q > 2))) :=
  ⟨(-2 : ℤ), (0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q > 2))) :=
  ⟨(-1 : ℤ), (1/2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q > 2))) :=
  ⟨(1 : ℤ), (3 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q > 2))) :=
  ⟨(2 : ℤ), (2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q > 2))) :=
  ⟨(3 : ℤ), (1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q > 2))) :=
  ⟨(-2 : ℤ), (-1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q > 2))) :=
  ⟨(1 : ℤ), (1/2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q > 2))) :=
  ⟨(2 : ℤ), (3 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q > 2))) :=
  ⟨(3 : ℤ), (2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q > 2))) :=
  ⟨(-2 : ℤ), (1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q > 2))) :=
  ⟨(2 : ℤ), (1/2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q > 2))) :=
  ⟨(3 : ℤ), (3 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ), ¬((2 ≤ q) ↔ (q > 2)) :=
  ⟨(2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ), ¬((2 ≤ q) ↔ (q > 2)) :=
  ⟨(1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ), ¬((2 ≤ q) ↔ (q > 2)) :=
  ⟨(3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ), ¬((2 ≤ q) ↔ (q > 2)) :=
  ⟨(0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ), ¬((2 ≤ q) ↔ (q > 2)) :=
  ⟨(-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ), ¬((2 ≤ q) ↔ (q > 2)) :=
  ⟨(-2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℤ) (hq : q ≥ 3) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : q ≥ 3) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : q ≥ 3) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : q ≥ 3) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : q ≥ 3) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : q ≥ 3) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : q ≥ 3) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : q ≥ 3) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (q ≥ 3) := by
  omega

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (q ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (q ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (q ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (q ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (q ≥ 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (q ≥ 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q ≥ 3))) :=
  ⟨(0 : ℤ), (0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q ≥ 3))) :=
  ⟨(0 : ℤ), (-1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q ≥ 3))) :=
  ⟨(-1 : ℤ), (0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q ≥ 3))) :=
  ⟨(0 : ℤ), (1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q ≥ 3))) :=
  ⟨(-1 : ℤ), (-1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q ≥ 3))) :=
  ⟨(1 : ℤ), (0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q ≥ 3))) :=
  ⟨(0 : ℤ), (2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q ≥ 3))) :=
  ⟨(-1 : ℤ), (1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q ≥ 3))) :=
  ⟨(1 : ℤ), (-1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q ≥ 3))) :=
  ⟨(2 : ℤ), (0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q ≥ 3))) :=
  ⟨(0 : ℤ), (3 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q ≥ 3))) :=
  ⟨(-1 : ℤ), (2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q ≥ 3))) :=
  ⟨(1 : ℤ), (1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q ≥ 3))) :=
  ⟨(2 : ℤ), (-1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q ≥ 3))) :=
  ⟨(3 : ℤ), (0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q ≥ 3))) :=
  ⟨(0 : ℤ), (4 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q ≥ 3))) :=
  ⟨(-1 : ℤ), (3 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q ≥ 3))) :=
  ⟨(1 : ℤ), (2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q ≥ 3))) :=
  ⟨(2 : ℤ), (1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q ≥ 3))) :=
  ⟨(3 : ℤ), (-1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q ≥ 3))) :=
  ⟨(4 : ℤ), (0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q ≥ 3))) :=
  ⟨(0 : ℤ), (1/2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q ≥ 3))) :=
  ⟨(-1 : ℤ), (4 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q ≥ 3))) :=
  ⟨(1 : ℤ), (3 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q ≥ 3))) :=
  ⟨(2 : ℤ), (2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q ≥ 3))) :=
  ⟨(3 : ℤ), (1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q ≥ 3))) :=
  ⟨(4 : ℤ), (-1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q ≥ 3))) :=
  ⟨(-2 : ℤ), (0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q ≥ 3))) :=
  ⟨(-1 : ℤ), (1/2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q ≥ 3))) :=
  ⟨(1 : ℤ), (4 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q ≥ 3))) :=
  ⟨(2 : ℤ), (3 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (q ≥ 3))) :=
  ⟨(3 : ℤ), (2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ), ¬((2 ≤ q) ↔ (q ≥ 3)) :=
  ⟨(2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ), ¬((2 ≤ q) ↔ (q ≥ 3)) :=
  ⟨(1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ), ¬((2 ≤ q) ↔ (q ≥ 3)) :=
  ⟨(3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ), ¬((2 ≤ q) ↔ (q ≥ 3)) :=
  ⟨(4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ), ¬((2 ≤ q) ↔ (q ≥ 3)) :=
  ⟨(0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ), ¬((2 ≤ q) ↔ (q ≥ 3)) :=
  ⟨(-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ), ¬((2 ≤ q) ↔ (q ≥ 3)) :=
  ⟨(-2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℤ) (hq : 1 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 1 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 1 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 1 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 1 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 1 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 1 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (hq : 1 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (1 ≤ q) := by
  omega

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (1 ≤ q) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (1 ≤ q) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (1 ≤ q) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (1 ≤ q) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (1 ≤ q) := by
  simp_all

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (1 ≤ q) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (1 ≤ q))) :=
  ⟨(0 : ℤ), (0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (1 ≤ q))) :=
  ⟨(0 : ℤ), (-1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (1 ≤ q))) :=
  ⟨(-1 : ℤ), (0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (1 ≤ q))) :=
  ⟨(0 : ℤ), (1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (1 ≤ q))) :=
  ⟨(-1 : ℤ), (-1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (1 ≤ q))) :=
  ⟨(1 : ℤ), (0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (1 ≤ q))) :=
  ⟨(0 : ℤ), (2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (1 ≤ q))) :=
  ⟨(-1 : ℤ), (1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (1 ≤ q))) :=
  ⟨(1 : ℤ), (-1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (1 ≤ q))) :=
  ⟨(2 : ℤ), (0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (1 ≤ q))) :=
  ⟨(0 : ℤ), (3 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (1 ≤ q))) :=
  ⟨(-1 : ℤ), (2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (1 ≤ q))) :=
  ⟨(1 : ℤ), (1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (1 ≤ q))) :=
  ⟨(2 : ℤ), (-1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (1 ≤ q))) :=
  ⟨(3 : ℤ), (0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (1 ≤ q))) :=
  ⟨(0 : ℤ), (1/2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (1 ≤ q))) :=
  ⟨(-1 : ℤ), (3 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (1 ≤ q))) :=
  ⟨(1 : ℤ), (2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (1 ≤ q))) :=
  ⟨(2 : ℤ), (1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (1 ≤ q))) :=
  ⟨(3 : ℤ), (-1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (1 ≤ q))) :=
  ⟨(-2 : ℤ), (0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (1 ≤ q))) :=
  ⟨(-1 : ℤ), (1/2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (1 ≤ q))) :=
  ⟨(1 : ℤ), (3 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (1 ≤ q))) :=
  ⟨(2 : ℤ), (2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (1 ≤ q))) :=
  ⟨(3 : ℤ), (1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (1 ≤ q))) :=
  ⟨(-2 : ℤ), (-1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (1 ≤ q))) :=
  ⟨(1 : ℤ), (1/2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (1 ≤ q))) :=
  ⟨(2 : ℤ), (3 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (1 ≤ q))) :=
  ⟨(3 : ℤ), (2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (1 ≤ q))) :=
  ⟨(-2 : ℤ), (1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (1 ≤ q))) :=
  ⟨(2 : ℤ), (1/2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (1 ≤ q))) :=
  ⟨(3 : ℤ), (3 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ), ¬((2 ≤ q) ↔ (1 ≤ q)) :=
  ⟨(2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ), ¬((2 ≤ q) ↔ (1 ≤ q)) :=
  ⟨(1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ), ¬((2 ≤ q) ↔ (1 ≤ q)) :=
  ⟨(3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ), ¬((2 ≤ q) ↔ (1 ≤ q)) :=
  ⟨(0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ), ¬((2 ≤ q) ↔ (1 ≤ q)) :=
  ⟨(-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ), ¬((2 ≤ q) ↔ (1 ≤ q)) :=
  ⟨(-2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℤ) (r : ℚ) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) (hr : r ≠ 0), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (r : ℚ) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) (hr : r ≠ 0), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (r : ℚ) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) (hr : r ≠ 0), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (r : ℚ) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) (hr : r ≠ 0), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (r : ℚ) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) (hr : r ≠ 0), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (r : ℚ) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) (hr : r ≠ 0), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (r : ℚ) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) (hr : r ≠ 0), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℤ) (r : ℚ) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) (hr : r ≠ 0), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) →
    (∀ (q : ℤ) (hq : 2 ≤ q) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)), Irrational (∑' n : ℕ, (1 : ℝ) / ((q : ℝ) ^ (n + 1) + (r : ℝ)))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    (2 ≤ q) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(0 : ℤ), (0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(0 : ℤ), (-1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(-1 : ℤ), (0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(0 : ℤ), (1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(-1 : ℤ), (-1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(1 : ℤ), (0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(0 : ℤ), (2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(-1 : ℤ), (1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(1 : ℤ), (-1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(2 : ℤ), (0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(0 : ℤ), (3 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(-1 : ℤ), (2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(1 : ℤ), (1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(2 : ℤ), (-1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(3 : ℤ), (0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(0 : ℤ), (1/2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(-1 : ℤ), (3 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(1 : ℤ), (2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(2 : ℤ), (1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(3 : ℤ), (-1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(-2 : ℤ), (0 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(-1 : ℤ), (1/2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(1 : ℤ), (3 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(2 : ℤ), (2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(3 : ℤ), (1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(-2 : ℤ), (-1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(1 : ℤ), (1/2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(2 : ℤ), (3 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(3 : ℤ), (2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(-2 : ℤ), (1 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(2 : ℤ), (1/2 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ) (r : ℚ), (r ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) ∧ (¬((2 ≤ q) ↔ (True))) :=
  ⟨(3 : ℤ), (3 : ℚ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ), ¬((2 ≤ q) ↔ (True)) :=
  ⟨(2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ), ¬((2 ≤ q) ↔ (True)) :=
  ⟨(1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ), ¬((2 ≤ q) ↔ (True)) :=
  ⟨(3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ), ¬((2 ≤ q) ↔ (True)) :=
  ⟨(0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ), ¬((2 ≤ q) ↔ (True)) :=
  ⟨(-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (q : ℤ), ¬((2 ≤ q) ↔ (True)) :=
  ⟨(-2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hq : 2 ≤ q) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hq : 2 ≤ q) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hq : 2 ≤ q) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hq : 2 ≤ q) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (q : ℤ) (r : ℚ) (hq : 2 ≤ q) (hr : r ≠ 0) (hne : ∀ n : ℕ, 1 ≤ n → r ≠ -((q : ℚ) ^ n)) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
