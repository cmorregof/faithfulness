import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.NumberTheory.AutomaticNumber
--   import FormalConjecturesForMathlib.NumberTheory.MultiplicativelyIndependent
/-!
# Bugeaud Collection of Conjectures and Open Questions: Automatic Expansions in Two Bases

Problem 10.32 asks whether some irrational real number has automatic expansions in two
multiplicatively independent bases. The answer is no. Adamczewski and Faverjon [AF20] proved
it with the multivariate Mahler method, in a form that is stronger than the question asked:
the base-$b$ digit sequence may be $k$-automatic for an arbitrary $k \ge 2$, not only for
$k = b$.

The definitions used here are in `FormalConjecturesForMathlib`:
`Nat.MultiplicativelyIndependent` and `Nat.MultiplicativelyIndependentFamily`,
`AutomaticSequence.IsAutomatic`, `AutomaticSequence.IsAutomaticInBase` and
`AutomaticSequence.IsBroadlyAutomaticInBase`.

*References:*
  - [AF20](https://arxiv.org/abs/2012.08283) Adamczewski, Boris, and Colin Faverjon.
    "Mahler's method in several variables and finite automata." arXiv:2012.08283 (2020).
    Appendix A, Conjectures A.2 and A.3, both proved there from Part (i) of Theorem 1.1.
  - [AS03] Allouche, Jean-Paul, and Jeffrey Shallit. "Automatic Sequences: Theory,
    Applications, Generalizations." Cambridge University Press, 2003. Chapter 13,
    Open Problems 7, p. 403, is the problem that Problem 10.32 modifies.
  - [Bug12] Bugeaud, Yann. "Distribution modulo one and Diophantine approximation."
    Vol. 193. Cambridge University Press, 2012. Chapter 10.
  - [Cob69] Cobham, Alan. "On the base-dependence of sets of numbers recognizable by finite
    automata." Mathematical Systems Theory 3 (1969): 186-192.
  - [LvdP82] Loxton, John H., and Alfred J. van der Poorten. "Arithmetic properties of the
    solutions of a class of functional equations." Journal für die reine und angewandte
    Mathematik 330 (1982): 159-172. Its transcendence method was the first attack on the
    problem; Nishioka later reported a gap in its main proof.
-/

section

namespace Bugeaud32

open AutomaticSequence

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) →
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) →
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) →
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) →
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) →
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) →
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) →
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    (2 ≤ b₁) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    (2 ≤ b₁) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    (2 ≤ b₁) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    (2 ≤ b₁) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    (2 ≤ b₁) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    (2 ≤ b₁) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    (2 ≤ b₁) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (True))) :=
  ⟨(2 : ℝ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (True))) :=
  ⟨(2 : ℝ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (True))) :=
  ⟨(2 : ℝ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (True))) :=
  ⟨(1 : ℝ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (True))) :=
  ⟨(2 : ℝ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (True))) :=
  ⟨(2 : ℝ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (True))) :=
  ⟨(2 : ℝ), (3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (True))) :=
  ⟨(1 : ℝ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (True))) :=
  ⟨(3 : ℝ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (True))) :=
  ⟨(2 : ℝ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (True))) :=
  ⟨(2 : ℝ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (True))) :=
  ⟨(2 : ℝ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (True))) :=
  ⟨(2 : ℝ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (True))) :=
  ⟨(1 : ℝ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (True))) :=
  ⟨(1 : ℝ), (3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (True))) :=
  ⟨(3 : ℝ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (True))) :=
  ⟨(3 : ℝ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (True))) :=
  ⟨(0 : ℝ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (True))) :=
  ⟨(2 : ℝ), (2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (True))) :=
  ⟨(2 : ℝ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (True))) :=
  ⟨(2 : ℝ), (3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (True))) :=
  ⟨(2 : ℝ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (True))) :=
  ⟨(2 : ℝ), (5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (True))) :=
  ⟨(1 : ℝ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (True))) :=
  ⟨(1 : ℝ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (True))) :=
  ⟨(3 : ℝ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (True))) :=
  ⟨(3 : ℝ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (True))) :=
  ⟨(3 : ℝ), (3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b₁ : ℕ), ¬((2 ≤ b₁) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b₁ : ℕ), ¬((2 ≤ b₁) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b₁ : ℕ), ¬((2 ≤ b₁) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b₁ : ℕ), ¬((2 ≤ b₁) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b₁ : ℕ), ¬((2 ≤ b₁) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b₁ : ℕ), ¬((2 ≤ b₁) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 3 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) →
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 3 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) →
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 3 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) →
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 3 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) →
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 3 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) →
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 3 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) →
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 3 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) →
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 3 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    (2 ≤ b₁) ↔ (3 ≤ b₁) := by
  omega

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    (2 ≤ b₁) ↔ (3 ≤ b₁) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    (2 ≤ b₁) ↔ (3 ≤ b₁) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    (2 ≤ b₁) ↔ (3 ≤ b₁) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    (2 ≤ b₁) ↔ (3 ≤ b₁) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    (2 ≤ b₁) ↔ (3 ≤ b₁) := by
  simp_all

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    (2 ≤ b₁) ↔ (3 ≤ b₁) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (3 ≤ b₁))) :=
  ⟨(2 : ℝ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (3 ≤ b₁))) :=
  ⟨(2 : ℝ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (3 ≤ b₁))) :=
  ⟨(2 : ℝ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (3 ≤ b₁))) :=
  ⟨(1 : ℝ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (3 ≤ b₁))) :=
  ⟨(2 : ℝ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (3 ≤ b₁))) :=
  ⟨(2 : ℝ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (3 ≤ b₁))) :=
  ⟨(2 : ℝ), (3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (3 ≤ b₁))) :=
  ⟨(1 : ℝ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (3 ≤ b₁))) :=
  ⟨(1 : ℝ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (3 ≤ b₁))) :=
  ⟨(3 : ℝ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (3 ≤ b₁))) :=
  ⟨(2 : ℝ), (2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (3 ≤ b₁))) :=
  ⟨(2 : ℝ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (3 ≤ b₁))) :=
  ⟨(2 : ℝ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (3 ≤ b₁))) :=
  ⟨(2 : ℝ), (4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (3 ≤ b₁))) :=
  ⟨(1 : ℝ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (3 ≤ b₁))) :=
  ⟨(1 : ℝ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (3 ≤ b₁))) :=
  ⟨(1 : ℝ), (3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (3 ≤ b₁))) :=
  ⟨(3 : ℝ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (3 ≤ b₁))) :=
  ⟨(3 : ℝ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (3 ≤ b₁))) :=
  ⟨(4 : ℝ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (3 ≤ b₁))) :=
  ⟨(2 : ℝ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (3 ≤ b₁))) :=
  ⟨(2 : ℝ), (1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (3 ≤ b₁))) :=
  ⟨(2 : ℝ), (3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (3 ≤ b₁))) :=
  ⟨(2 : ℝ), (4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (3 ≤ b₁))) :=
  ⟨(2 : ℝ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (3 ≤ b₁))) :=
  ⟨(1 : ℝ), (2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (3 ≤ b₁))) :=
  ⟨(1 : ℝ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (3 ≤ b₁))) :=
  ⟨(1 : ℝ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (3 ≤ b₁))) :=
  ⟨(1 : ℝ), (4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (3 ≤ b₁))) :=
  ⟨(3 : ℝ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (3 ≤ b₁))) :=
  ⟨(3 : ℝ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (3 ≤ b₁))) :=
  ⟨(3 : ℝ), (3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b₁ : ℕ), ¬((2 ≤ b₁) ↔ (3 ≤ b₁)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b₁ : ℕ), ¬((2 ≤ b₁) ↔ (3 ≤ b₁)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b₁ : ℕ), ¬((2 ≤ b₁) ↔ (3 ≤ b₁)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b₁ : ℕ), ¬((2 ≤ b₁) ↔ (3 ≤ b₁)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b₁ : ℕ), ¬((2 ≤ b₁) ↔ (3 ≤ b₁)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b₁ : ℕ), ¬((2 ≤ b₁) ↔ (3 ≤ b₁)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b₁ : ℕ), ¬((2 ≤ b₁) ↔ (3 ≤ b₁)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : b₁ ≥ 2) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) :
    (2 ≤ b₁) ↔ (b₁ ≥ 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) :
    (2 ≤ b₁) ↔ (b₁ ≥ 2) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) :
    (2 ≤ b₁) ↔ (b₁ ≥ 2) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) :
    (2 ≤ b₁) ↔ (b₁ ≥ 2) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) :
    (2 ≤ b₁) ↔ (b₁ ≥ 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) :
    (2 ≤ b₁) ↔ (b₁ ≥ 2) := by
  omega

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) :
    (2 ≤ b₁) ↔ (b₁ ≥ 2) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) :
    (2 ≤ b₁) ↔ (b₁ ≥ 2) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) ↔
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : b₁ ≥ 2) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) ↔
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : b₁ ≥ 2) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) ↔
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : b₁ ≥ 2) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) ↔
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : b₁ ≥ 2) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₂ : 2 ≤ b₂) (hb₁ : 2 ≤ b₁) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) ↔
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₂ : 2 ≤ b₂) (hb₁ : 2 ≤ b₁) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) ↔
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₂ : 2 ≤ b₂) (hb₁ : 2 ≤ b₁) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) ↔
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₂ : 2 ≤ b₂) (hb₁ : 2 ≤ b₁) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) ↔
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₂ : 2 ≤ b₂) (hb₁ : 2 ≤ b₁) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ξ : ℝ) (hξ₀ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) ↔
    (∀ (ξ : ℝ) (hξ₀ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) ↔
    (∀ (ξ : ℝ) (hξ₀ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) ↔
    (∀ (ξ : ℝ) (hξ₀ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) ↔
    (∀ (ξ : ℝ) (hξ₀ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : ¬(b₁ < 2)) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) :
    (2 ≤ b₁) ↔ (¬(b₁ < 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) :
    (2 ≤ b₁) ↔ (¬(b₁ < 2)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) :
    (2 ≤ b₁) ↔ (¬(b₁ < 2)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) :
    (2 ≤ b₁) ↔ (¬(b₁ < 2)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) :
    (2 ≤ b₁) ↔ (¬(b₁ < 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) :
    (2 ≤ b₁) ↔ (¬(b₁ < 2)) := by
  omega

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) :
    (2 ≤ b₁) ↔ (¬(b₁ < 2)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) :
    (2 ≤ b₁) ↔ (¬(b₁ < 2)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) ↔
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : ¬(b₁ < 2)) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) ↔
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : ¬(b₁ < 2)) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) ↔
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : ¬(b₁ < 2)) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) ↔
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : ¬(b₁ < 2)) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 1 < b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) :
    (2 ≤ b₁) ↔ (1 < b₁) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) :
    (2 ≤ b₁) ↔ (1 < b₁) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) :
    (2 ≤ b₁) ↔ (1 < b₁) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) :
    (2 ≤ b₁) ↔ (1 < b₁) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) :
    (2 ≤ b₁) ↔ (1 < b₁) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) :
    (2 ≤ b₁) ↔ (1 < b₁) := by
  omega

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) :
    (2 ≤ b₁) ↔ (1 < b₁) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) :
    (2 ≤ b₁) ↔ (1 < b₁) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) ↔
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 1 < b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) ↔
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 1 < b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) ↔
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 1 < b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) ↔
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 1 < b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : b₁ ≥ 3) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) →
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : b₁ ≥ 3) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) →
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : b₁ ≥ 3) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) →
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : b₁ ≥ 3) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) →
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : b₁ ≥ 3) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) →
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : b₁ ≥ 3) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) →
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : b₁ ≥ 3) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) →
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : b₁ ≥ 3) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    (2 ≤ b₁) ↔ (b₁ ≥ 3) := by
  omega

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    (2 ≤ b₁) ↔ (b₁ ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    (2 ≤ b₁) ↔ (b₁ ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    (2 ≤ b₁) ↔ (b₁ ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    (2 ≤ b₁) ↔ (b₁ ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    (2 ≤ b₁) ↔ (b₁ ≥ 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    (2 ≤ b₁) ↔ (b₁ ≥ 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (b₁ ≥ 3))) :=
  ⟨(2 : ℝ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (b₁ ≥ 3))) :=
  ⟨(2 : ℝ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (b₁ ≥ 3))) :=
  ⟨(2 : ℝ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (b₁ ≥ 3))) :=
  ⟨(1 : ℝ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (b₁ ≥ 3))) :=
  ⟨(2 : ℝ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (b₁ ≥ 3))) :=
  ⟨(2 : ℝ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (b₁ ≥ 3))) :=
  ⟨(2 : ℝ), (3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (b₁ ≥ 3))) :=
  ⟨(1 : ℝ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (b₁ ≥ 3))) :=
  ⟨(1 : ℝ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (b₁ ≥ 3))) :=
  ⟨(3 : ℝ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (b₁ ≥ 3))) :=
  ⟨(2 : ℝ), (2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (b₁ ≥ 3))) :=
  ⟨(2 : ℝ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (b₁ ≥ 3))) :=
  ⟨(2 : ℝ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (b₁ ≥ 3))) :=
  ⟨(2 : ℝ), (4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (b₁ ≥ 3))) :=
  ⟨(1 : ℝ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (b₁ ≥ 3))) :=
  ⟨(1 : ℝ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (b₁ ≥ 3))) :=
  ⟨(1 : ℝ), (3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (b₁ ≥ 3))) :=
  ⟨(3 : ℝ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (b₁ ≥ 3))) :=
  ⟨(3 : ℝ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (b₁ ≥ 3))) :=
  ⟨(4 : ℝ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (b₁ ≥ 3))) :=
  ⟨(2 : ℝ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (b₁ ≥ 3))) :=
  ⟨(2 : ℝ), (1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (b₁ ≥ 3))) :=
  ⟨(2 : ℝ), (3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (b₁ ≥ 3))) :=
  ⟨(2 : ℝ), (4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (b₁ ≥ 3))) :=
  ⟨(2 : ℝ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (b₁ ≥ 3))) :=
  ⟨(1 : ℝ), (2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (b₁ ≥ 3))) :=
  ⟨(1 : ℝ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (b₁ ≥ 3))) :=
  ⟨(1 : ℝ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (b₁ ≥ 3))) :=
  ⟨(1 : ℝ), (4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (b₁ ≥ 3))) :=
  ⟨(3 : ℝ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (b₁ ≥ 3))) :=
  ⟨(3 : ℝ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₂) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₁) ↔ (b₁ ≥ 3))) :=
  ⟨(3 : ℝ), (3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b₁ : ℕ), ¬((2 ≤ b₁) ↔ (b₁ ≥ 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b₁ : ℕ), ¬((2 ≤ b₁) ↔ (b₁ ≥ 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b₁ : ℕ), ¬((2 ≤ b₁) ↔ (b₁ ≥ 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b₁ : ℕ), ¬((2 ≤ b₁) ↔ (b₁ ≥ 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b₁ : ℕ), ¬((2 ≤ b₁) ↔ (b₁ ≥ 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b₁ : ℕ), ¬((2 ≤ b₁) ↔ (b₁ ≥ 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b₁ : ℕ), ¬((2 ≤ b₁) ↔ (b₁ ≥ 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 1 < b₁) (hb₂ : 3 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) →
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 1 < b₁) (hb₂ : 3 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) →
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 1 < b₁) (hb₂ : 3 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) →
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 1 < b₁) (hb₂ : 3 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) →
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 1 < b₁) (hb₂ : 3 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) →
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 1 < b₁) (hb₂ : 3 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) →
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 1 < b₁) (hb₂ : 3 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) →
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 1 < b₁) (hb₂ : 3 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₁ : 2 ≤ b₁) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    (2 ≤ b₂) ↔ (3 ≤ b₂) := by
  omega

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₁ : 2 ≤ b₁) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    (2 ≤ b₂) ↔ (3 ≤ b₂) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₁ : 2 ≤ b₁) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    (2 ≤ b₂) ↔ (3 ≤ b₂) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₁ : 2 ≤ b₁) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    (2 ≤ b₂) ↔ (3 ≤ b₂) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₁ : 2 ≤ b₁) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    (2 ≤ b₂) ↔ (3 ≤ b₂) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₁ : 2 ≤ b₁) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    (2 ≤ b₂) ↔ (3 ≤ b₂) := by
  simp_all

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₁ : 2 ≤ b₁) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    (2 ≤ b₂) ↔ (3 ≤ b₂) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (3 ≤ b₂))) :=
  ⟨(2 : ℝ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (3 ≤ b₂))) :=
  ⟨(2 : ℝ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (3 ≤ b₂))) :=
  ⟨(2 : ℝ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (3 ≤ b₂))) :=
  ⟨(1 : ℝ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (3 ≤ b₂))) :=
  ⟨(2 : ℝ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (3 ≤ b₂))) :=
  ⟨(2 : ℝ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (3 ≤ b₂))) :=
  ⟨(2 : ℝ), (3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (3 ≤ b₂))) :=
  ⟨(1 : ℝ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (3 ≤ b₂))) :=
  ⟨(1 : ℝ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (3 ≤ b₂))) :=
  ⟨(3 : ℝ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (3 ≤ b₂))) :=
  ⟨(2 : ℝ), (2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (3 ≤ b₂))) :=
  ⟨(2 : ℝ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (3 ≤ b₂))) :=
  ⟨(2 : ℝ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (3 ≤ b₂))) :=
  ⟨(2 : ℝ), (4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (3 ≤ b₂))) :=
  ⟨(1 : ℝ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (3 ≤ b₂))) :=
  ⟨(1 : ℝ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (3 ≤ b₂))) :=
  ⟨(1 : ℝ), (3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (3 ≤ b₂))) :=
  ⟨(3 : ℝ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (3 ≤ b₂))) :=
  ⟨(3 : ℝ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (3 ≤ b₂))) :=
  ⟨(4 : ℝ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (3 ≤ b₂))) :=
  ⟨(2 : ℝ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (3 ≤ b₂))) :=
  ⟨(2 : ℝ), (1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (3 ≤ b₂))) :=
  ⟨(2 : ℝ), (3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (3 ≤ b₂))) :=
  ⟨(2 : ℝ), (4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (3 ≤ b₂))) :=
  ⟨(2 : ℝ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (3 ≤ b₂))) :=
  ⟨(1 : ℝ), (2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (3 ≤ b₂))) :=
  ⟨(1 : ℝ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (3 ≤ b₂))) :=
  ⟨(1 : ℝ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (3 ≤ b₂))) :=
  ⟨(1 : ℝ), (4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (3 ≤ b₂))) :=
  ⟨(3 : ℝ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (3 ≤ b₂))) :=
  ⟨(3 : ℝ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (3 ≤ b₂))) :=
  ⟨(3 : ℝ), (3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b₂ : ℕ), ¬((2 ≤ b₂) ↔ (3 ≤ b₂)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b₂ : ℕ), ¬((2 ≤ b₂) ↔ (3 ≤ b₂)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b₂ : ℕ), ¬((2 ≤ b₂) ↔ (3 ≤ b₂)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b₂ : ℕ), ¬((2 ≤ b₂) ↔ (3 ≤ b₂)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b₂ : ℕ), ¬((2 ≤ b₂) ↔ (3 ≤ b₂)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b₂ : ℕ), ¬((2 ≤ b₂) ↔ (3 ≤ b₂)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b₂ : ℕ), ¬((2 ≤ b₂) ↔ (3 ≤ b₂)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 1 < b₁) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 1 < b₁) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) →
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 1 < b₁) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) →
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 1 < b₁) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) →
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 1 < b₁) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) →
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 1 < b₁) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) →
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 1 < b₁) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) →
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 1 < b₁) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) →
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₁ : 2 ≤ b₁) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    (2 ≤ b₂) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₁ : 2 ≤ b₁) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    (2 ≤ b₂) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₁ : 2 ≤ b₁) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    (2 ≤ b₂) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₁ : 2 ≤ b₁) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    (2 ≤ b₂) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₁ : 2 ≤ b₁) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    (2 ≤ b₂) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₁ : 2 ≤ b₁) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    (2 ≤ b₂) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₁ : 2 ≤ b₁) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    (2 ≤ b₂) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(2 : ℝ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(2 : ℝ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(2 : ℝ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(1 : ℝ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(2 : ℝ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(2 : ℝ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(2 : ℝ), (3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(1 : ℝ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(3 : ℝ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(2 : ℝ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(2 : ℝ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(2 : ℝ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(2 : ℝ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(1 : ℝ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(1 : ℝ), (3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(3 : ℝ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(3 : ℝ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(0 : ℝ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(2 : ℝ), (2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(2 : ℝ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(2 : ℝ), (3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(2 : ℝ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(2 : ℝ), (5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(1 : ℝ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(1 : ℝ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(3 : ℝ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(3 : ℝ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(3 : ℝ), (3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b₂ : ℕ), ¬((2 ≤ b₂) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b₂ : ℕ), ¬((2 ≤ b₂) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b₂ : ℕ), ¬((2 ≤ b₂) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b₂ : ℕ), ¬((2 ≤ b₂) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b₂ : ℕ), ¬((2 ≤ b₂) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b₂ : ℕ), ¬((2 ≤ b₂) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) →
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) →
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) →
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) →
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) →
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) →
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) →
    (∀ (ξ : ℝ) (hξ : Irrational ξ) (b₁ b₂ : ℕ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ), False) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₁ : 2 ≤ b₁) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    (2 ≤ b₂) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₁ : 2 ≤ b₁) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    (2 ≤ b₂) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₁ : 2 ≤ b₁) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    (2 ≤ b₂) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₁ : 2 ≤ b₁) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    (2 ≤ b₂) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₁ : 2 ≤ b₁) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    (2 ≤ b₂) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₁ : 2 ≤ b₁) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    (2 ≤ b₂) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₁ : 2 ≤ b₁) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    (2 ≤ b₂) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(2 : ℝ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(2 : ℝ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(2 : ℝ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(1 : ℝ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(2 : ℝ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(2 : ℝ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(2 : ℝ), (3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(1 : ℝ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(3 : ℝ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(2 : ℝ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(2 : ℝ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(2 : ℝ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(2 : ℝ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(1 : ℝ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(1 : ℝ), (3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(3 : ℝ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(3 : ℝ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(0 : ℝ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(2 : ℝ), (2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(2 : ℝ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(2 : ℝ), (3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(2 : ℝ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(2 : ℝ), (5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(1 : ℝ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(1 : ℝ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(3 : ℝ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(3 : ℝ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ξ : ℝ) (b₁ : ℕ) (b₂ : ℕ), (Irrational ξ) ∧ (2 ≤ b₁) ∧ (Nat.MultiplicativelyIndependent b₁ b₂) ∧ (IsBroadlyAutomaticInBase b₁ ξ) ∧ (IsBroadlyAutomaticInBase b₂ ξ) ∧ (¬((2 ≤ b₂) ↔ (True))) :=
  ⟨(3 : ℝ), (3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b₂ : ℕ), ¬((2 ≤ b₂) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b₂ : ℕ), ¬((2 ≤ b₂) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b₂ : ℕ), ¬((2 ≤ b₂) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b₂ : ℕ), ¬((2 ≤ b₂) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b₂ : ℕ), ¬((2 ≤ b₂) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b₂ : ℕ), ¬((2 ≤ b₂) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (ξ : ℝ) (b₁ b₂ : ℕ) (hξ : Irrational ξ) (hb₁ : 2 ≤ b₁) (hb₂ : 2 ≤ b₂) (hind : Nat.MultiplicativelyIndependent b₁ b₂) (h₁ : IsBroadlyAutomaticInBase b₁ ξ) (h₂ : IsBroadlyAutomaticInBase b₂ ξ) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
