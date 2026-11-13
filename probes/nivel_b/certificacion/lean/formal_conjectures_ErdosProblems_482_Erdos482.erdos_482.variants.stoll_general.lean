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

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w) :
    (2 ≤ g) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w) :
    (2 ≤ g) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w) :
    (2 ≤ g) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w) :
    (2 ≤ g) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w) :
    (2 ≤ g) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w) :
    (2 ≤ g) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w) :
    (2 ≤ g) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (True))) :=
  ⟨(0 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (True))) :=
  ⟨(1 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (True))) :=
  ⟨(2 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (True))) :=
  ⟨(3 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (True))) :=
  ⟨(3 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (True))) :=
  ⟨(5 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (True))) :=
  ⟨(0 : ℕ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (True))) :=
  ⟨(3 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (True))) :=
  ⟨(5 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (True))) :=
  ⟨(10 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (True))) :=
  ⟨(1 : ℕ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (True))) :=
  ⟨(2 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (True))) :=
  ⟨(3 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (True))) :=
  ⟨(5 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (True))) :=
  ⟨(10 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (True))) :=
  ⟨(2 : ℕ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (True))) :=
  ⟨(3 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (True))) :=
  ⟨(5 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (True))) :=
  ⟨(10 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (True))) :=
  ⟨(3 : ℕ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (True))) :=
  ⟨(5 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ), ¬((2 ≤ g) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ), ¬((2 ≤ g) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ), ¬((2 ≤ g) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ), ¬((2 ≤ g) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ), ¬((2 ≤ g) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ), ¬((2 ≤ g) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 ≤ w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 ≤ w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 ≤ w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 ≤ w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 ≤ w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 ≤ w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 ≤ w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 ≤ w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hg : 2 ≤ g) :
    (0 < w) ↔ (0 ≤ w) := by
  omega

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hg : 2 ≤ g) :
    (0 < w) ↔ (0 ≤ w) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hg : 2 ≤ g) :
    (0 < w) ↔ (0 ≤ w) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hg : 2 ≤ g) :
    (0 < w) ↔ (0 ≤ w) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hg : 2 ≤ g) :
    (0 < w) ↔ (0 ≤ w) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hg : 2 ≤ g) :
    (0 < w) ↔ (0 ≤ w) := by
  simp_all

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hg : 2 ≤ g) :
    (0 < w) ↔ (0 ≤ w) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(2 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(2 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(1 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(2 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(1 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(3 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(2 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(1 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(3 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(0 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(2 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(1 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(3 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(0 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(5 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(2 : ℕ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(1 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(3 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(0 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(5 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(10 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(1 : ℕ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(3 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(0 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(5 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(10 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(3 : ℕ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(0 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(5 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(10 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(0 : ℕ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(5 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (w : ℝ), ¬((0 < w) ↔ (0 ≤ w)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (w : ℝ), ¬((0 < w) ↔ (0 ≤ w)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (w : ℝ), ¬((0 < w) ↔ (0 ≤ w)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (w : ℝ), ¬((0 < w) ↔ (0 ≤ w)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (w : ℝ), ¬((0 < w) ↔ (0 ≤ w)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (w : ℝ), ¬((0 < w) ↔ (0 ≤ w)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (g : ℕ) [NeZero g] (hg : 2 < g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 2 < g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 2 < g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 2 < g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 2 < g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 2 < g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 2 < g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 2 < g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w) :
    (2 ≤ g) ↔ (2 < g) := by
  omega

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w) :
    (2 ≤ g) ↔ (2 < g) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w) :
    (2 ≤ g) ↔ (2 < g) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w) :
    (2 ≤ g) ↔ (2 < g) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w) :
    (2 ≤ g) ↔ (2 < g) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w) :
    (2 ≤ g) ↔ (2 < g) := by
  simp_all

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w) :
    (2 ≤ g) ↔ (2 < g) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (2 < g))) :=
  ⟨(0 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (2 < g))) :=
  ⟨(0 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (2 < g))) :=
  ⟨(1 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (2 < g))) :=
  ⟨(0 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (2 < g))) :=
  ⟨(1 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (2 < g))) :=
  ⟨(2 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (2 < g))) :=
  ⟨(0 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (2 < g))) :=
  ⟨(1 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (2 < g))) :=
  ⟨(2 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (2 < g))) :=
  ⟨(3 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (2 < g))) :=
  ⟨(0 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (2 < g))) :=
  ⟨(1 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (2 < g))) :=
  ⟨(2 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (2 < g))) :=
  ⟨(3 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (2 < g))) :=
  ⟨(5 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (2 < g))) :=
  ⟨(0 : ℕ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (2 < g))) :=
  ⟨(1 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (2 < g))) :=
  ⟨(2 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (2 < g))) :=
  ⟨(3 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (2 < g))) :=
  ⟨(5 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (2 < g))) :=
  ⟨(10 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (2 < g))) :=
  ⟨(1 : ℕ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (2 < g))) :=
  ⟨(2 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (2 < g))) :=
  ⟨(3 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (2 < g))) :=
  ⟨(5 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (2 < g))) :=
  ⟨(10 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (2 < g))) :=
  ⟨(2 : ℕ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (2 < g))) :=
  ⟨(3 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (2 < g))) :=
  ⟨(5 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (2 < g))) :=
  ⟨(10 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (2 < g))) :=
  ⟨(3 : ℕ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (2 < g))) :=
  ⟨(5 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ), ¬((2 ≤ g) ↔ (2 < g)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ), ¬((2 ≤ g) ↔ (2 < g)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ), ¬((2 ≤ g) ↔ (2 < g)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ), ¬((2 ≤ g) ↔ (2 < g)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ), ¬((2 ≤ g) ↔ (2 < g)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ), ¬((2 ≤ g) ↔ (2 < g)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (g : ℕ) [NeZero g] (hg : 3 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 3 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 3 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 3 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 3 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 3 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 3 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 3 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w) :
    (2 ≤ g) ↔ (3 ≤ g) := by
  omega

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w) :
    (2 ≤ g) ↔ (3 ≤ g) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w) :
    (2 ≤ g) ↔ (3 ≤ g) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w) :
    (2 ≤ g) ↔ (3 ≤ g) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w) :
    (2 ≤ g) ↔ (3 ≤ g) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w) :
    (2 ≤ g) ↔ (3 ≤ g) := by
  simp_all

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w) :
    (2 ≤ g) ↔ (3 ≤ g) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (3 ≤ g))) :=
  ⟨(0 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (3 ≤ g))) :=
  ⟨(0 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (3 ≤ g))) :=
  ⟨(1 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (3 ≤ g))) :=
  ⟨(0 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (3 ≤ g))) :=
  ⟨(1 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (3 ≤ g))) :=
  ⟨(2 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (3 ≤ g))) :=
  ⟨(0 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (3 ≤ g))) :=
  ⟨(1 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (3 ≤ g))) :=
  ⟨(2 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (3 ≤ g))) :=
  ⟨(3 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (3 ≤ g))) :=
  ⟨(0 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (3 ≤ g))) :=
  ⟨(1 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (3 ≤ g))) :=
  ⟨(2 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (3 ≤ g))) :=
  ⟨(3 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (3 ≤ g))) :=
  ⟨(4 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (3 ≤ g))) :=
  ⟨(0 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (3 ≤ g))) :=
  ⟨(1 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (3 ≤ g))) :=
  ⟨(2 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (3 ≤ g))) :=
  ⟨(3 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (3 ≤ g))) :=
  ⟨(4 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (3 ≤ g))) :=
  ⟨(5 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (3 ≤ g))) :=
  ⟨(0 : ℕ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (3 ≤ g))) :=
  ⟨(1 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (3 ≤ g))) :=
  ⟨(2 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (3 ≤ g))) :=
  ⟨(3 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (3 ≤ g))) :=
  ⟨(4 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (3 ≤ g))) :=
  ⟨(5 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (3 ≤ g))) :=
  ⟨(10 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (3 ≤ g))) :=
  ⟨(1 : ℕ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (3 ≤ g))) :=
  ⟨(2 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (3 ≤ g))) :=
  ⟨(3 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (3 ≤ g))) :=
  ⟨(4 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ), ¬((2 ≤ g) ↔ (3 ≤ g)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ), ¬((2 ≤ g) ↔ (3 ≤ g)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ), ¬((2 ≤ g) ↔ (3 ≤ g)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ), ¬((2 ≤ g) ↔ (3 ≤ g)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ), ¬((2 ≤ g) ↔ (3 ≤ g)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ), ¬((2 ≤ g) ↔ (3 ≤ g)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ), ¬((2 ≤ g) ↔ (3 ≤ g)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (g : ℕ) [NeZero g] (hg : g ≥ 2) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) :
    (2 ≤ g) ↔ (g ≥ 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) :
    (2 ≤ g) ↔ (g ≥ 2) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) :
    (2 ≤ g) ↔ (g ≥ 2) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) :
    (2 ≤ g) ↔ (g ≥ 2) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) :
    (2 ≤ g) ↔ (g ≥ 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) :
    (2 ≤ g) ↔ (g ≥ 2) := by
  omega

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) :
    (2 ≤ g) ↔ (g ≥ 2) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) :
    (2 ≤ g) ↔ (g ≥ 2) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔
    (∀ (g : ℕ) [NeZero g] (hg : g ≥ 2) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔
    (∀ (g : ℕ) [NeZero g] (hg : g ≥ 2) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔
    (∀ (g : ℕ) [NeZero g] (hg : g ≥ 2) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔
    (∀ (g : ℕ) [NeZero g] (hg : g ≥ 2) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a₁ b ε : ℝ, a₁ * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a₁ b ε (2 * n) - g * generalRecurrence g a₁ b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) :
    (∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔ (∃ a₁ b ε : ℝ, a₁ * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a₁ b ε (2 * n) - g * generalRecurrence g a₁ b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) :
    (∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔ (∃ a₁ b ε : ℝ, a₁ * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a₁ b ε (2 * n) - g * generalRecurrence g a₁ b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) :
    (∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔ (∃ a₁ b ε : ℝ, a₁ * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a₁ b ε (2 * n) - g * generalRecurrence g a₁ b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) :
    (∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔ (∃ a₁ b ε : ℝ, a₁ * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a₁ b ε (2 * n) - g * generalRecurrence g a₁ b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) :
    (∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔ (∃ a₁ b ε : ℝ, a₁ * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a₁ b ε (2 * n) - g * generalRecurrence g a₁ b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) :
    (∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔ (∃ a₁ b ε : ℝ, a₁ * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a₁ b ε (2 * n) - g * generalRecurrence g a₁ b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  omega

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) :
    (∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔ (∃ a₁ b ε : ℝ, a₁ * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a₁ b ε (2 * n) - g * generalRecurrence g a₁ b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) :
    (∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔ (∃ a₁ b ε : ℝ, a₁ * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a₁ b ε (2 * n) - g * generalRecurrence g a₁ b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a₁ b ε : ℝ, a₁ * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a₁ b ε (2 * n) - g * generalRecurrence g a₁ b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a₁ b ε : ℝ, a₁ * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a₁ b ε (2 * n) - g * generalRecurrence g a₁ b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a₁ b ε : ℝ, a₁ * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a₁ b ε (2 * n) - g * generalRecurrence g a₁ b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a₁ b ε : ℝ, a₁ * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a₁ b ε (2 * n) - g * generalRecurrence g a₁ b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (g : ℕ) [NeZero g] (hg₀ : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔
    (∀ (g : ℕ) [NeZero g] (hg₀ : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔
    (∀ (g : ℕ) [NeZero g] (hg₀ : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔
    (∀ (g : ℕ) [NeZero g] (hg₀ : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔
    (∀ (g : ℕ) [NeZero g] (hg₀ : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (g : ℕ) [NeZero g] (hg : ¬(g < 2)) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) :
    (2 ≤ g) ↔ (¬(g < 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) :
    (2 ≤ g) ↔ (¬(g < 2)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) :
    (2 ≤ g) ↔ (¬(g < 2)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) :
    (2 ≤ g) ↔ (¬(g < 2)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) :
    (2 ≤ g) ↔ (¬(g < 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) :
    (2 ≤ g) ↔ (¬(g < 2)) := by
  omega

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) :
    (2 ≤ g) ↔ (¬(g < 2)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) :
    (2 ≤ g) ↔ (¬(g < 2)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔
    (∀ (g : ℕ) [NeZero g] (hg : ¬(g < 2)) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔
    (∀ (g : ℕ) [NeZero g] (hg : ¬(g < 2)) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔
    (∀ (g : ℕ) [NeZero g] (hg : ¬(g < 2)) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔
    (∀ (g : ℕ) [NeZero g] (hg : ¬(g < 2)) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (g : ℕ) [NeZero g] (hg : 1 < g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) :
    (2 ≤ g) ↔ (1 < g) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) :
    (2 ≤ g) ↔ (1 < g) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) :
    (2 ≤ g) ↔ (1 < g) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) :
    (2 ≤ g) ↔ (1 < g) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) :
    (2 ≤ g) ↔ (1 < g) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) :
    (2 ≤ g) ↔ (1 < g) := by
  omega

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) :
    (2 ≤ g) ↔ (1 < g) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) :
    (2 ≤ g) ↔ (1 < g) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔
    (∀ (g : ℕ) [NeZero g] (hg : 1 < g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔
    (∀ (g : ℕ) [NeZero g] (hg : 1 < g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔
    (∀ (g : ℕ) [NeZero g] (hg : 1 < g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔
    (∀ (g : ℕ) [NeZero g] (hg : 1 < g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (g : ℕ) [NeZero g] (hg : g ≥ 2) (w : ℝ) (hw : 0 ≤ w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : g ≥ 2) (w : ℝ) (hw : 0 ≤ w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : g ≥ 2) (w : ℝ) (hw : 0 ≤ w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : g ≥ 2) (w : ℝ) (hw : 0 ≤ w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : g ≥ 2) (w : ℝ) (hw : 0 ≤ w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : g ≥ 2) (w : ℝ) (hw : 0 ≤ w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : g ≥ 2) (w : ℝ) (hw : 0 ≤ w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : g ≥ 2) (w : ℝ) (hw : 0 ≤ w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hg : 2 ≤ g) :
    (0 < w) ↔ (0 ≤ w) := by
  omega

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hg : 2 ≤ g) :
    (0 < w) ↔ (0 ≤ w) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hg : 2 ≤ g) :
    (0 < w) ↔ (0 ≤ w) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hg : 2 ≤ g) :
    (0 < w) ↔ (0 ≤ w) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hg : 2 ≤ g) :
    (0 < w) ↔ (0 ≤ w) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hg : 2 ≤ g) :
    (0 < w) ↔ (0 ≤ w) := by
  simp_all

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hg : 2 ≤ g) :
    (0 < w) ↔ (0 ≤ w) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(2 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(2 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(1 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(2 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(1 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(3 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(2 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(1 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(3 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(0 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(2 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(1 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(3 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(0 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(5 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(2 : ℕ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(1 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(3 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(0 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(5 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(10 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(1 : ℕ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(3 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(0 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(5 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(10 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(3 : ℕ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(0 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(5 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(10 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(0 : ℕ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (¬((0 < w) ↔ (0 ≤ w))) :=
  ⟨(5 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (w : ℝ), ¬((0 < w) ↔ (0 ≤ w)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (w : ℝ), ¬((0 < w) ↔ (0 ≤ w)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (w : ℝ), ¬((0 < w) ↔ (0 ≤ w)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (w : ℝ), ¬((0 < w) ↔ (0 ≤ w)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (w : ℝ), ¬((0 < w) ↔ (0 ≤ w)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (w : ℝ), ¬((0 < w) ↔ (0 ≤ w)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (g : ℕ) [NeZero g] (hg : g > 2) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : g > 2) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : g > 2) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : g > 2) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : g > 2) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : g > 2) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : g > 2) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : g > 2) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w) :
    (2 ≤ g) ↔ (g > 2) := by
  omega

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w) :
    (2 ≤ g) ↔ (g > 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w) :
    (2 ≤ g) ↔ (g > 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w) :
    (2 ≤ g) ↔ (g > 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w) :
    (2 ≤ g) ↔ (g > 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w) :
    (2 ≤ g) ↔ (g > 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w) :
    (2 ≤ g) ↔ (g > 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g > 2))) :=
  ⟨(0 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g > 2))) :=
  ⟨(0 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g > 2))) :=
  ⟨(1 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g > 2))) :=
  ⟨(0 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g > 2))) :=
  ⟨(1 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g > 2))) :=
  ⟨(2 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g > 2))) :=
  ⟨(0 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g > 2))) :=
  ⟨(1 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g > 2))) :=
  ⟨(2 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g > 2))) :=
  ⟨(3 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g > 2))) :=
  ⟨(0 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g > 2))) :=
  ⟨(1 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g > 2))) :=
  ⟨(2 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g > 2))) :=
  ⟨(3 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g > 2))) :=
  ⟨(5 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g > 2))) :=
  ⟨(0 : ℕ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g > 2))) :=
  ⟨(1 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g > 2))) :=
  ⟨(2 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g > 2))) :=
  ⟨(3 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g > 2))) :=
  ⟨(5 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g > 2))) :=
  ⟨(10 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g > 2))) :=
  ⟨(1 : ℕ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g > 2))) :=
  ⟨(2 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g > 2))) :=
  ⟨(3 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g > 2))) :=
  ⟨(5 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g > 2))) :=
  ⟨(10 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g > 2))) :=
  ⟨(2 : ℕ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g > 2))) :=
  ⟨(3 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g > 2))) :=
  ⟨(5 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g > 2))) :=
  ⟨(10 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g > 2))) :=
  ⟨(3 : ℕ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g > 2))) :=
  ⟨(5 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ), ¬((2 ≤ g) ↔ (g > 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ), ¬((2 ≤ g) ↔ (g > 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ), ¬((2 ≤ g) ↔ (g > 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ), ¬((2 ≤ g) ↔ (g > 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ), ¬((2 ≤ g) ↔ (g > 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ), ¬((2 ≤ g) ↔ (g > 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (g : ℕ) [NeZero g] (hg : g ≥ 3) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : g ≥ 3) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : g ≥ 3) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : g ≥ 3) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : g ≥ 3) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : g ≥ 3) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : g ≥ 3) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : g ≥ 3) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w) :
    (2 ≤ g) ↔ (g ≥ 3) := by
  omega

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w) :
    (2 ≤ g) ↔ (g ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w) :
    (2 ≤ g) ↔ (g ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w) :
    (2 ≤ g) ↔ (g ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w) :
    (2 ≤ g) ↔ (g ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w) :
    (2 ≤ g) ↔ (g ≥ 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w) :
    (2 ≤ g) ↔ (g ≥ 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g ≥ 3))) :=
  ⟨(0 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g ≥ 3))) :=
  ⟨(0 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g ≥ 3))) :=
  ⟨(1 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g ≥ 3))) :=
  ⟨(0 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g ≥ 3))) :=
  ⟨(1 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g ≥ 3))) :=
  ⟨(2 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g ≥ 3))) :=
  ⟨(0 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g ≥ 3))) :=
  ⟨(1 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g ≥ 3))) :=
  ⟨(2 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g ≥ 3))) :=
  ⟨(3 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g ≥ 3))) :=
  ⟨(0 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g ≥ 3))) :=
  ⟨(1 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g ≥ 3))) :=
  ⟨(2 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g ≥ 3))) :=
  ⟨(3 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g ≥ 3))) :=
  ⟨(4 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g ≥ 3))) :=
  ⟨(0 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g ≥ 3))) :=
  ⟨(1 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g ≥ 3))) :=
  ⟨(2 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g ≥ 3))) :=
  ⟨(3 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g ≥ 3))) :=
  ⟨(4 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g ≥ 3))) :=
  ⟨(5 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g ≥ 3))) :=
  ⟨(0 : ℕ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g ≥ 3))) :=
  ⟨(1 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g ≥ 3))) :=
  ⟨(2 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g ≥ 3))) :=
  ⟨(3 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g ≥ 3))) :=
  ⟨(4 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g ≥ 3))) :=
  ⟨(5 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g ≥ 3))) :=
  ⟨(10 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g ≥ 3))) :=
  ⟨(1 : ℕ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g ≥ 3))) :=
  ⟨(2 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g ≥ 3))) :=
  ⟨(3 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (g ≥ 3))) :=
  ⟨(4 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ), ¬((2 ≤ g) ↔ (g ≥ 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ), ¬((2 ≤ g) ↔ (g ≥ 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ), ¬((2 ≤ g) ↔ (g ≥ 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ), ¬((2 ≤ g) ↔ (g ≥ 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ), ¬((2 ≤ g) ↔ (g ≥ 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ), ¬((2 ≤ g) ↔ (g ≥ 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ), ¬((2 ≤ g) ↔ (g ≥ 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (g : ℕ) [NeZero g] (hg : 1 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 1 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 1 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 1 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 1 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 1 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 1 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 1 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w) :
    (2 ≤ g) ↔ (1 ≤ g) := by
  omega

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w) :
    (2 ≤ g) ↔ (1 ≤ g) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w) :
    (2 ≤ g) ↔ (1 ≤ g) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w) :
    (2 ≤ g) ↔ (1 ≤ g) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w) :
    (2 ≤ g) ↔ (1 ≤ g) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w) :
    (2 ≤ g) ↔ (1 ≤ g) := by
  simp_all

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hw : 0 < w) :
    (2 ≤ g) ↔ (1 ≤ g) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (1 ≤ g))) :=
  ⟨(0 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (1 ≤ g))) :=
  ⟨(0 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (1 ≤ g))) :=
  ⟨(1 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (1 ≤ g))) :=
  ⟨(0 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (1 ≤ g))) :=
  ⟨(1 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (1 ≤ g))) :=
  ⟨(2 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (1 ≤ g))) :=
  ⟨(0 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (1 ≤ g))) :=
  ⟨(1 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (1 ≤ g))) :=
  ⟨(2 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (1 ≤ g))) :=
  ⟨(3 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (1 ≤ g))) :=
  ⟨(0 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (1 ≤ g))) :=
  ⟨(1 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (1 ≤ g))) :=
  ⟨(2 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (1 ≤ g))) :=
  ⟨(3 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (1 ≤ g))) :=
  ⟨(5 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (1 ≤ g))) :=
  ⟨(0 : ℕ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (1 ≤ g))) :=
  ⟨(1 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (1 ≤ g))) :=
  ⟨(2 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (1 ≤ g))) :=
  ⟨(3 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (1 ≤ g))) :=
  ⟨(5 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (1 ≤ g))) :=
  ⟨(10 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (1 ≤ g))) :=
  ⟨(1 : ℕ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (1 ≤ g))) :=
  ⟨(2 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (1 ≤ g))) :=
  ⟨(3 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (1 ≤ g))) :=
  ⟨(5 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (1 ≤ g))) :=
  ⟨(10 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (1 ≤ g))) :=
  ⟨(2 : ℕ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (1 ≤ g))) :=
  ⟨(3 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (1 ≤ g))) :=
  ⟨(5 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (1 ≤ g))) :=
  ⟨(10 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (1 ≤ g))) :=
  ⟨(3 : ℕ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (0 < w) ∧ (¬((2 ≤ g) ↔ (1 ≤ g))) :=
  ⟨(5 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ), ¬((2 ≤ g) ↔ (1 ≤ g)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ), ¬((2 ≤ g) ↔ (1 ≤ g)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ), ¬((2 ≤ g) ↔ (1 ≤ g)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ), ¬((2 ≤ g) ↔ (1 ≤ g)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ), ¬((2 ≤ g) ↔ (1 ≤ g)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ), ¬((2 ≤ g) ↔ (1 ≤ g)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (g : ℕ) [NeZero g] (hg : 1 < g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 1 < g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 1 < g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 1 < g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 1 < g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 1 < g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 1 < g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 1 < g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 1 < g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 1 < g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 1 < g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 1 < g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 1 < g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 1 < g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (g : ℕ) [NeZero g] (hg : 2 ≤ g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) →
    (∀ (g : ℕ) [NeZero g] (hg : 1 < g) (w : ℝ) (hw : 0 < w), ∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (0 < w) ∧ (¬(∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(2 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (0 < w) ∧ (¬(∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(2 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (0 < w) ∧ (¬(∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(1 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (0 < w) ∧ (¬(∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(2 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (0 < w) ∧ (¬(∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(1 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (0 < w) ∧ (¬(∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(3 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (0 < w) ∧ (¬(∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(2 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (0 < w) ∧ (¬(∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(1 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (0 < w) ∧ (¬(∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(3 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (0 < w) ∧ (¬(∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(0 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (0 < w) ∧ (¬(∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(2 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (0 < w) ∧ (¬(∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(1 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (0 < w) ∧ (¬(∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(3 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (0 < w) ∧ (¬(∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(0 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (0 < w) ∧ (¬(∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(4 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (0 < w) ∧ (¬(∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(2 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (0 < w) ∧ (¬(∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(1 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (0 < w) ∧ (¬(∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(3 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (0 < w) ∧ (¬(∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(0 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (0 < w) ∧ (¬(∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(4 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (0 < w) ∧ (¬(∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(5 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (0 < w) ∧ (¬(∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(2 : ℕ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (0 < w) ∧ (¬(∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(1 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (0 < w) ∧ (¬(∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(3 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (0 < w) ∧ (¬(∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(0 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (0 < w) ∧ (¬(∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(4 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (0 < w) ∧ (¬(∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(5 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (0 < w) ∧ (¬(∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(10 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (0 < w) ∧ (¬(∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(1 : ℕ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (0 < w) ∧ (¬(∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(3 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (0 < w) ∧ (¬(∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(0 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), (2 ≤ g) ∧ (0 < w) ∧ (¬(∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(4 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), ¬((∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔ (∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(1 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), ¬((∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔ (∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(1 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), ¬((∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔ (∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(0 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), ¬((∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔ (∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(1 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), ¬((∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔ (∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(0 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), ¬((∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔ (∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(2 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), ¬((∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔ (∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(1 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), ¬((∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔ (∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(0 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), ¬((∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔ (∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(2 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), ¬((∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔ (∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(3 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), ¬((∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔ (∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(1 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), ¬((∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔ (∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(0 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), ¬((∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔ (∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(2 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), ¬((∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔ (∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(3 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), ¬((∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔ (∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(4 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), ¬((∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔ (∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(1 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), ¬((∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔ (∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(0 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), ¬((∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔ (∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(2 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), ¬((∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔ (∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(3 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), ¬((∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔ (∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(4 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), ¬((∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔ (∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(5 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), ¬((∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔ (∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(1 : ℕ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), ¬((∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔ (∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(0 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), ¬((∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔ (∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(2 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), ¬((∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔ (∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(3 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), ¬((∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔ (∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(4 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), ¬((∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔ (∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(5 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), ¬((∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔ (∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(10 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), ¬((∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔ (∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(0 : ℕ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), ¬((∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔ (∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(2 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), ¬((∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔ (∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(3 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (g : ℕ) (w : ℝ), ¬((∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (2 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ)) ↔ (∃ a b ε : ℝ, a * b = g ∧
      ∀ n : ℕ, 1 ≤ n →
        generalRecurrence g a b ε (3 * n) - g * generalRecurrence g a b ε (2 * n - 2) =
          (Real.digits (w / (g : ℝ) ^ ⌊Real.logb g w⌋ * (g : ℝ) ^ (n - 1) / g) g 0 : ℕ))) :=
  ⟨(4 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hg : 2 ≤ g) (hw : 0 < w) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hg : 2 ≤ g) (hw : 0 < w) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hg : 2 ≤ g) (hw : 0 < w) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hg : 2 ≤ g) (hw : 0 < w) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (g : ℕ) [NeZero g] (w : ℝ) (hg : 2 ≤ g) (hw : 0 < w) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
