import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Data.Set.Density
/-!
# Erdős Problem 1149

*References:*
- [erdosproblems.com/1149](https://www.erdosproblems.com/1149)
- [BeRi17] Bergelson, Vitaly and Richter, Florian Karl, *On the density of coprime tuples of the
  form $(n,\lfloor f_1(n)\rfloor,\dots,\lfloor f_k(n)\rfloor)$, where $f_1,\dots,f_k$ are
  functions from a Hardy field*. Number Theory - Diophantine Problems, Uniform Distribution and
  Applications, Springer (2017), 109-135. [arXiv:1611.08044](https://arxiv.org/abs/1611.08044)
- [Va99] Various, *Some of Paul's favorite problems*. Booklet produced for the conference "Paul
  Erdős and his mathematics", Budapest, July 1999 (1999).
-/

section

namespace Erdos1149

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)) :
    (0 < α) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)) :
    (0 < α) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)) :
    (0 < α) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)) :
    (0 < α) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)) :
    (0 < α) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)) :
    (0 < α) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)) :
    (0 < α) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (α ∉ Set.range ((↑) : ℤ → ℝ)) ∧ (¬((0 < α) ↔ (True))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (α ∉ Set.range ((↑) : ℤ → ℝ)) ∧ (¬((0 < α) ↔ (True))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (α ∉ Set.range ((↑) : ℤ → ℝ)) ∧ (¬((0 < α) ↔ (True))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (α ∉ Set.range ((↑) : ℤ → ℝ)) ∧ (¬((0 < α) ↔ (True))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (α ∉ Set.range ((↑) : ℤ → ℝ)) ∧ (¬((0 < α) ↔ (True))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (α ∉ Set.range ((↑) : ℤ → ℝ)) ∧ (¬((0 < α) ↔ (True))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((0 < α) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((0 < α) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((0 < α) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((0 < α) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((0 < α) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((0 < α) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : 0 ≤ α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 ≤ α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 ≤ α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 ≤ α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 ≤ α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 ≤ α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 ≤ α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 ≤ α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)) :
    (0 < α) ↔ (0 ≤ α) := by
  omega

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)) :
    (0 < α) ↔ (0 ≤ α) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)) :
    (0 < α) ↔ (0 ≤ α) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)) :
    (0 < α) ↔ (0 ≤ α) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)) :
    (0 < α) ↔ (0 ≤ α) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)) :
    (0 < α) ↔ (0 ≤ α) := by
  simp_all

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)) :
    (0 < α) ↔ (0 ≤ α) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (α ∉ Set.range ((↑) : ℤ → ℝ)) ∧ (¬((0 < α) ↔ (0 ≤ α))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (α ∉ Set.range ((↑) : ℤ → ℝ)) ∧ (¬((0 < α) ↔ (0 ≤ α))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (α ∉ Set.range ((↑) : ℤ → ℝ)) ∧ (¬((0 < α) ↔ (0 ≤ α))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (α ∉ Set.range ((↑) : ℤ → ℝ)) ∧ (¬((0 < α) ↔ (0 ≤ α))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (α ∉ Set.range ((↑) : ℤ → ℝ)) ∧ (¬((0 < α) ↔ (0 ≤ α))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (α ∉ Set.range ((↑) : ℤ → ℝ)) ∧ (¬((0 < α) ↔ (0 ≤ α))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((0 < α) ↔ (0 ≤ α)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((0 < α) ↔ (0 ≤ α)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((0 < α) ↔ (0 ≤ α)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((0 < α) ↔ (0 ≤ α)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((0 < α) ↔ (0 ≤ α)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((0 < α) ↔ (0 ≤ α)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2)

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 < α) ∧ (α ∉ Set.range ((↑) : ℤ → ℝ)) ∧ (¬({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 < α) ∧ (α ∉ Set.range ((↑) : ℤ → ℝ)) ∧ (¬({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 < α) ∧ (α ∉ Set.range ((↑) : ℤ → ℝ)) ∧ (¬({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 < α) ∧ (α ∉ Set.range ((↑) : ℤ → ℝ)) ∧ (¬({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 < α) ∧ (α ∉ Set.range ((↑) : ℤ → ℝ)) ∧ (¬({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2))) :=
  ⟨(7 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 < α) ∧ (α ∉ Set.range ((↑) : ℤ → ℝ)) ∧ (¬({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2))) :=
  ⟨(6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 < α) ∧ (α ∉ Set.range ((↑) : ℤ → ℝ)) ∧ (¬({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2))) :=
  ⟨(8 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 < α) ∧ (α ∉ Set.range ((↑) : ℤ → ℝ)) ∧ (¬({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 < α) ∧ (α ∉ Set.range ((↑) : ℤ → ℝ)) ∧ (¬({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬(({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) ↔ ({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬(({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) ↔ ({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬(({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) ↔ ({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬(({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) ↔ ({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2))) :=
  ⟨(6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬(({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) ↔ ({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2))) :=
  ⟨(5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬(({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) ↔ ({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2))) :=
  ⟨(7 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬(({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) ↔ ({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬(({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) ↔ ({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2))) :=
  ⟨(8 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬(({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) ↔ ({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬(({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) ↔ ({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : α > 0) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (α > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (α > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (α > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (α > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (α > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (α > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (α > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (α > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) ↔
    (∀ (α : ℝ) (hα : α > 0) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) ↔
    (∀ (α : ℝ) (hα : α > 0) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) ↔
    (∀ (α : ℝ) (hα : α > 0) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) ↔
    (∀ (α : ℝ) (hα : α > 0) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)) (hα : 0 < α), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) ↔
    (∀ (α : ℝ) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)) (hα : 0 < α), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) ↔
    (∀ (α : ℝ) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)) (hα : 0 < α), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) ↔
    (∀ (α : ℝ) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)) (hα : 0 < α), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) ↔
    (∀ (α : ℝ) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)) (hα : 0 < α), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα₀ : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) ↔
    (∀ (α : ℝ) (hα₀ : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) ↔
    (∀ (α : ℝ) (hα₀ : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) ↔
    (∀ (α : ℝ) (hα₀ : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) ↔
    (∀ (α : ℝ) (hα₀ : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : ¬(α ≤ 0)) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (¬(α ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (¬(α ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (¬(α ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (¬(α ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (¬(α ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (¬(α ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (¬(α ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (¬(α ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) ↔
    (∀ (α : ℝ) (hα : ¬(α ≤ 0)) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) ↔
    (∀ (α : ℝ) (hα : ¬(α ≤ 0)) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) ↔
    (∀ (α : ℝ) (hα : ¬(α ≤ 0)) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) ↔
    (∀ (α : ℝ) (hα : ¬(α ≤ 0)) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : α ≥ 0) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : α ≥ 0) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : α ≥ 0) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : α ≥ 0) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : α ≥ 0) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : α ≥ 0) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : α ≥ 0) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : α ≥ 0) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)) :
    (0 < α) ↔ (α ≥ 0) := by
  omega

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)) :
    (0 < α) ↔ (α ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)) :
    (0 < α) ↔ (α ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)) :
    (0 < α) ↔ (α ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)) :
    (0 < α) ↔ (α ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)) :
    (0 < α) ↔ (α ≥ 0) := by
  simp_all

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)) :
    (0 < α) ↔ (α ≥ 0) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (α ∉ Set.range ((↑) : ℤ → ℝ)) ∧ (¬((0 < α) ↔ (α ≥ 0))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (α ∉ Set.range ((↑) : ℤ → ℝ)) ∧ (¬((0 < α) ↔ (α ≥ 0))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (α ∉ Set.range ((↑) : ℤ → ℝ)) ∧ (¬((0 < α) ↔ (α ≥ 0))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (α ∉ Set.range ((↑) : ℤ → ℝ)) ∧ (¬((0 < α) ↔ (α ≥ 0))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (α ∉ Set.range ((↑) : ℤ → ℝ)) ∧ (¬((0 < α) ↔ (α ≥ 0))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (α ∉ Set.range ((↑) : ℤ → ℝ)) ∧ (¬((0 < α) ↔ (α ≥ 0))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((0 < α) ↔ (α ≥ 0)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((0 < α) ↔ (α ≥ 0)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((0 < α) ↔ (α ≥ 0)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((0 < α) ↔ (α ≥ 0)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((0 < α) ↔ (α ≥ 0)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((0 < α) ↔ (α ≥ 0)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : α > 0) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2)

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : α > 0) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : α > 0) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : α > 0) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : α > 0) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : α > 0) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : α > 0) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : α > 0) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : α > 0) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : α > 0) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : α > 0) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : α > 0) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : α > 0) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : α > 0) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) →
    (∀ (α : ℝ) (hα : α > 0) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)), {n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 < α) ∧ (α ∉ Set.range ((↑) : ℤ → ℝ)) ∧ (¬({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 < α) ∧ (α ∉ Set.range ((↑) : ℤ → ℝ)) ∧ (¬({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 < α) ∧ (α ∉ Set.range ((↑) : ℤ → ℝ)) ∧ (¬({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 < α) ∧ (α ∉ Set.range ((↑) : ℤ → ℝ)) ∧ (¬({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 < α) ∧ (α ∉ Set.range ((↑) : ℤ → ℝ)) ∧ (¬({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2))) :=
  ⟨(7 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 < α) ∧ (α ∉ Set.range ((↑) : ℤ → ℝ)) ∧ (¬({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2))) :=
  ⟨(6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 < α) ∧ (α ∉ Set.range ((↑) : ℤ → ℝ)) ∧ (¬({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2))) :=
  ⟨(8 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 < α) ∧ (α ∉ Set.range ((↑) : ℤ → ℝ)) ∧ (¬({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 < α) ∧ (α ∉ Set.range ((↑) : ℤ → ℝ)) ∧ (¬({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬(({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) ↔ ({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬(({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) ↔ ({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬(({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) ↔ ({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬(({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) ↔ ({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2))) :=
  ⟨(6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬(({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) ↔ ({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2))) :=
  ⟨(5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬(({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) ↔ ({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2))) :=
  ⟨(7 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬(({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) ↔ ({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬(({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) ↔ ({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2))) :=
  ⟨(8 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬(({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) ↔ ({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬(({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (6 / Real.pi ^ 2)) ↔ ({n : ℕ | 1 ≤ n ∧ n.Coprime ⌊(n : ℝ) ^ α⌋₊}.HasDensity (7 / Real.pi ^ 2))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα : 0 < α) (hα' : α ∉ Set.range ((↑) : ℤ → ℝ)) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
