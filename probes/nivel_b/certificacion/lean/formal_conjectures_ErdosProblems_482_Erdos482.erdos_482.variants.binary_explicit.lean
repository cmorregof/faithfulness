import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 482

*References:*
- [erdosproblems.com/482](https://www.erdosproblems.com/482)
- [GrPo70] Graham, R. L. and Pollak, H. O., Note on a nonlinear recurrence related to {$\surd 2$}. Math. Mag. (1970), 143-145.
- [St05] Stoll, Th., On families of nonlinear recurrences related to digits. J. Integer Seq. (2005), Article 05.3.2, 8.
- [St06] Stoll, Thomas, On a problem of Erd\H{o}s and Graham concerning digits. Acta Arith. (2006), 89-100.
- [RaGi91] Rabinowitz, S. and Gilbert, P., A nonlinear recurrence yielding binary digits. Math. Mag.
  64 (1991), 168-171.

A formal Lean proof is given in an external repository,
[`gotrevor/lean-gallery`](https://github.com/gotrevor/lean-gallery), formalized by Trevor Morris with
Claude Code.
-/

section

namespace Erdos482

/-- The sequence of the problem: $a_1 = 1$ and $a_{n+1} = \lfloor \sqrt{2}(a_n + 1/2) \rfloor$ for
$n \geq 1$. The value $a_0$ is not used. -/
noncomputable def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => ⌊√2 * ((a (n + 1) : ℝ) + 1 / 2)⌋₊

/-- Stoll's general Graham–Pollak-type recurrence in base $g$, with real parameters $a$, $b$, and
$\varepsilon$. Its even-index differences are used to read base-$g$ digits. -/
noncomputable def generalRecurrence (g : ℕ) (a b ε : ℝ) : ℕ → ℤ
  | 0 => 1
  | n + 1 =>
      if Even n then ⌊a * ((generalRecurrence g a b ε n : ℝ) + ε)⌋
      else ⌊b * ((generalRecurrence g a b ε n : ℝ) + 1 / ((g : ℝ) - 1))⌋

/-- The odd-step coefficient of the Rabinowitz–Gilbert/Stoll binary recurrence. -/
noncomputable def alpha (t : ℝ) : ℝ := 2 * (t + 1) / (t + 2)

/-- The even-step coefficient of the Rabinowitz–Gilbert/Stoll binary recurrence. -/
noncomputable def beta (t : ℝ) : ℝ := (t + 2) / (t + 1)

/-- Zero-based form of the Rabinowitz–Gilbert/Stoll binary recurrence: `stollBinary t k` is the
paper's $u_{k+1}$.  At $t = \sqrt{2}$ both coefficients equal $\sqrt{2}$, and this is the sequence
`a` shifted by one. -/
noncomputable def stollBinary (t : ℝ) : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      ⌊(if Even n then alpha t else beta t) * ((stollBinary t n : ℝ) + 1 / 2)⌋₊

/-- The binary digits of a normalized real $t \in [1, 2)$, indexed from one and including the
leading digit.  The value at index zero is padding. -/
noncomputable def binaryDigit (t : ℝ) : ℕ → Fin 2
  | 0 => 0
  | 1 => 1
  | k + 2 => Real.digits (t - 1) 2 k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (t : ℝ) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) →
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) →
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) →
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) →
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) →
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) →
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) →
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (t : ℝ) (ht2 : t < 2) :
    (1 ≤ t) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (t : ℝ) (ht2 : t < 2) :
    (1 ≤ t) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (t : ℝ) (ht2 : t < 2) :
    (1 ≤ t) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (t : ℝ) (ht2 : t < 2) :
    (1 ≤ t) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (t : ℝ) (ht2 : t < 2) :
    (1 ≤ t) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (t : ℝ) (ht2 : t < 2) :
    (1 ≤ t) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (t : ℝ) (ht2 : t < 2) :
    (1 ≤ t) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (t < 2) ∧ (¬((1 ≤ t) ↔ (True))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (t < 2) ∧ (¬((1 ≤ t) ↔ (True))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (t < 2) ∧ (¬((1 ≤ t) ↔ (True))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (t < 2) ∧ (¬((1 ≤ t) ↔ (True))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (t < 2) ∧ (¬((1 ≤ t) ↔ (True))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (t < 2) ∧ (¬((1 ≤ t) ↔ (True))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 ≤ t) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 ≤ t) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 ≤ t) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 ≤ t) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 ≤ t) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 ≤ t) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 3), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 3), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) →
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 3), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) →
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 3), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) →
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 3), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) →
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 3), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) →
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 3), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) →
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 3), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) →
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (t : ℝ) (ht1 : 1 ≤ t) :
    (t < 2) ↔ (t < 3) := by
  omega

set_option maxHeartbeats 200000 in
example (t : ℝ) (ht1 : 1 ≤ t) :
    (t < 2) ↔ (t < 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (t : ℝ) (ht1 : 1 ≤ t) :
    (t < 2) ↔ (t < 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (t : ℝ) (ht1 : 1 ≤ t) :
    (t < 2) ↔ (t < 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (t : ℝ) (ht1 : 1 ≤ t) :
    (t < 2) ↔ (t < 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (t : ℝ) (ht1 : 1 ≤ t) :
    (t < 2) ↔ (t < 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (t : ℝ) (ht1 : 1 ≤ t) :
    (t < 2) ↔ (t < 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (1 ≤ t) ∧ (¬((t < 2) ↔ (t < 3))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (1 ≤ t) ∧ (¬((t < 2) ↔ (t < 3))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (1 ≤ t) ∧ (¬((t < 2) ↔ (t < 3))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (1 ≤ t) ∧ (¬((t < 2) ↔ (t < 3))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (1 ≤ t) ∧ (¬((t < 2) ↔ (t < 3))) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (1 ≤ t) ∧ (¬((t < 2) ↔ (t < 3))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (1 ≤ t) ∧ (¬((t < 2) ↔ (t < 3))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((t < 2) ↔ (t < 3)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((t < 2) ↔ (t < 3)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((t < 2) ↔ (t < 3)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((t < 2) ↔ (t < 3)) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((t < 2) ↔ (t < 3)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((t < 2) ↔ (t < 3)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((t < 2) ↔ (t < 3)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (t : ℝ) (ht1 : t ≥ 1) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1

set_option maxHeartbeats 200000 in
example (t : ℝ) :
    (1 ≤ t) ↔ (t ≥ 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (t : ℝ) :
    (1 ≤ t) ↔ (t ≥ 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (t : ℝ) :
    (1 ≤ t) ↔ (t ≥ 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (t : ℝ) :
    (1 ≤ t) ↔ (t ≥ 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (t : ℝ) :
    (1 ≤ t) ↔ (t ≥ 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (t : ℝ) :
    (1 ≤ t) ↔ (t ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example (t : ℝ) :
    (1 ≤ t) ↔ (t ≥ 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (t : ℝ) :
    (1 ≤ t) ↔ (t ≥ 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) ↔
    (∀ (t : ℝ) (ht1 : t ≥ 1) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) ↔
    (∀ (t : ℝ) (ht1 : t ≥ 1) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) ↔
    (∀ (t : ℝ) (ht1 : t ≥ 1) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) ↔
    (∀ (t : ℝ) (ht1 : t ≥ 1) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n₁, 1 ≤ n₁ →
        stollBinary t (2 * n₁) - 2 * stollBinary t (2 * n₁ - 2) = (binaryDigit t n₁).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1

set_option maxHeartbeats 200000 in
example (t : ℝ) :
    ((∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) ↔ ((∀ n₁, 1 ≤ n₁ →
        stollBinary t (2 * n₁) - 2 * stollBinary t (2 * n₁ - 2) = (binaryDigit t n₁).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (t : ℝ) :
    ((∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) ↔ ((∀ n₁, 1 ≤ n₁ →
        stollBinary t (2 * n₁) - 2 * stollBinary t (2 * n₁ - 2) = (binaryDigit t n₁).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (t : ℝ) :
    ((∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) ↔ ((∀ n₁, 1 ≤ n₁ →
        stollBinary t (2 * n₁) - 2 * stollBinary t (2 * n₁ - 2) = (binaryDigit t n₁).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (t : ℝ) :
    ((∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) ↔ ((∀ n₁, 1 ≤ n₁ →
        stollBinary t (2 * n₁) - 2 * stollBinary t (2 * n₁ - 2) = (binaryDigit t n₁).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (t : ℝ) :
    ((∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) ↔ ((∀ n₁, 1 ≤ n₁ →
        stollBinary t (2 * n₁) - 2 * stollBinary t (2 * n₁ - 2) = (binaryDigit t n₁).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (t : ℝ) :
    ((∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) ↔ ((∀ n₁, 1 ≤ n₁ →
        stollBinary t (2 * n₁) - 2 * stollBinary t (2 * n₁ - 2) = (binaryDigit t n₁).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  omega

set_option maxHeartbeats 200000 in
example (t : ℝ) :
    ((∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) ↔ ((∀ n₁, 1 ≤ n₁ →
        stollBinary t (2 * n₁) - 2 * stollBinary t (2 * n₁ - 2) = (binaryDigit t n₁).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (t : ℝ) :
    ((∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) ↔ ((∀ n₁, 1 ≤ n₁ →
        stollBinary t (2 * n₁) - 2 * stollBinary t (2 * n₁ - 2) = (binaryDigit t n₁).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) ↔
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n₁, 1 ≤ n₁ →
        stollBinary t (2 * n₁) - 2 * stollBinary t (2 * n₁ - 2) = (binaryDigit t n₁).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) ↔
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n₁, 1 ≤ n₁ →
        stollBinary t (2 * n₁) - 2 * stollBinary t (2 * n₁ - 2) = (binaryDigit t n₁).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) ↔
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n₁, 1 ≤ n₁ →
        stollBinary t (2 * n₁) - 2 * stollBinary t (2 * n₁ - 2) = (binaryDigit t n₁).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) ↔
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n₁, 1 ≤ n₁ →
        stollBinary t (2 * n₁) - 2 * stollBinary t (2 * n₁ - 2) = (binaryDigit t n₁).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (t : ℝ) (ht2 : t < 2) (ht1 : 1 ≤ t), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) ↔
    (∀ (t : ℝ) (ht2 : t < 2) (ht1 : 1 ≤ t), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) ↔
    (∀ (t : ℝ) (ht2 : t < 2) (ht1 : 1 ≤ t), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) ↔
    (∀ (t : ℝ) (ht2 : t < 2) (ht1 : 1 ≤ t), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) ↔
    (∀ (t : ℝ) (ht2 : t < 2) (ht1 : 1 ≤ t), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (t : ℝ) (ht1' : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) ↔
    (∀ (t : ℝ) (ht1' : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) ↔
    (∀ (t : ℝ) (ht1' : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) ↔
    (∀ (t : ℝ) (ht1' : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) ↔
    (∀ (t : ℝ) (ht1' : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (t : ℝ) (ht1 : ¬(t < 1)) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1

set_option maxHeartbeats 200000 in
example (t : ℝ) :
    (1 ≤ t) ↔ (¬(t < 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (t : ℝ) :
    (1 ≤ t) ↔ (¬(t < 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (t : ℝ) :
    (1 ≤ t) ↔ (¬(t < 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (t : ℝ) :
    (1 ≤ t) ↔ (¬(t < 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (t : ℝ) :
    (1 ≤ t) ↔ (¬(t < 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (t : ℝ) :
    (1 ≤ t) ↔ (¬(t < 1)) := by
  omega

set_option maxHeartbeats 200000 in
example (t : ℝ) :
    (1 ≤ t) ↔ (¬(t < 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (t : ℝ) :
    (1 ≤ t) ↔ (¬(t < 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) ↔
    (∀ (t : ℝ) (ht1 : ¬(t < 1)) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) ↔
    (∀ (t : ℝ) (ht1 : ¬(t < 1)) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) ↔
    (∀ (t : ℝ) (ht1 : ¬(t < 1)) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) ↔
    (∀ (t : ℝ) (ht1 : ¬(t < 1)) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (t : ℝ) (ht1 : t ≥ 1) (ht2 : t < 3), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht1 : t ≥ 1) (ht2 : t < 3), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) →
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht1 : t ≥ 1) (ht2 : t < 3), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) →
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht1 : t ≥ 1) (ht2 : t < 3), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) →
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht1 : t ≥ 1) (ht2 : t < 3), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) →
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht1 : t ≥ 1) (ht2 : t < 3), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) →
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht1 : t ≥ 1) (ht2 : t < 3), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) →
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht1 : t ≥ 1) (ht2 : t < 3), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) →
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (t : ℝ) (ht1 : 1 ≤ t) :
    (t < 2) ↔ (t < 3) := by
  omega

set_option maxHeartbeats 200000 in
example (t : ℝ) (ht1 : 1 ≤ t) :
    (t < 2) ↔ (t < 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (t : ℝ) (ht1 : 1 ≤ t) :
    (t < 2) ↔ (t < 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (t : ℝ) (ht1 : 1 ≤ t) :
    (t < 2) ↔ (t < 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (t : ℝ) (ht1 : 1 ≤ t) :
    (t < 2) ↔ (t < 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (t : ℝ) (ht1 : 1 ≤ t) :
    (t < 2) ↔ (t < 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (t : ℝ) (ht1 : 1 ≤ t) :
    (t < 2) ↔ (t < 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (1 ≤ t) ∧ (¬((t < 2) ↔ (t < 3))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (1 ≤ t) ∧ (¬((t < 2) ↔ (t < 3))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (1 ≤ t) ∧ (¬((t < 2) ↔ (t < 3))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (1 ≤ t) ∧ (¬((t < 2) ↔ (t < 3))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (1 ≤ t) ∧ (¬((t < 2) ↔ (t < 3))) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (1 ≤ t) ∧ (¬((t < 2) ↔ (t < 3))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (1 ≤ t) ∧ (¬((t < 2) ↔ (t < 3))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((t < 2) ↔ (t < 3)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((t < 2) ↔ (t < 3)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((t < 2) ↔ (t < 3)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((t < 2) ↔ (t < 3)) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((t < 2) ↔ (t < 3)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((t < 2) ↔ (t < 3)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((t < 2) ↔ (t < 3)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (t : ℝ) (ht1 : 1 ≤ t), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht1 : 1 ≤ t), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) →
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht1 : 1 ≤ t), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) →
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht1 : 1 ≤ t), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) →
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht1 : 1 ≤ t), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) →
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht1 : 1 ≤ t), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) →
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht1 : 1 ≤ t), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) →
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (t : ℝ) (ht1 : 1 ≤ t), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) →
    (∀ (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2), (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (t : ℝ) (ht1 : 1 ≤ t) :
    (t < 2) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (t : ℝ) (ht1 : 1 ≤ t) :
    (t < 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (t : ℝ) (ht1 : 1 ≤ t) :
    (t < 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (t : ℝ) (ht1 : 1 ≤ t) :
    (t < 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (t : ℝ) (ht1 : 1 ≤ t) :
    (t < 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (t : ℝ) (ht1 : 1 ≤ t) :
    (t < 2) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (t : ℝ) (ht1 : 1 ≤ t) :
    (t < 2) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (1 ≤ t) ∧ (¬((t < 2) ↔ (True))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (1 ≤ t) ∧ (¬((t < 2) ↔ (True))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (1 ≤ t) ∧ (¬((t < 2) ↔ (True))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (1 ≤ t) ∧ (¬((t < 2) ↔ (True))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (1 ≤ t) ∧ (¬((t < 2) ↔ (True))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (1 ≤ t) ∧ (¬((t < 2) ↔ (True))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((t < 2) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((t < 2) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((t < 2) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((t < 2) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((t < 2) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((t < 2) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
