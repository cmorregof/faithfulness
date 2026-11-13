import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 400

*Reference:* [erdosproblems.com/400](https://www.erdosproblems.com/400)
-/

section

open Nat Filter Finset
open scoped Asymptotics Topology

namespace Erdos400

/--
For any $k\geq 2$ let $g_k(n)$ denote the maximum value of $(a_1+\cdots+a_k)-n$
where $a_1,\ldots,a_k$ are integers such that $a_1!\cdots a_k! \mid n!$.
-/
noncomputable def g (k n : ℕ) : ℕ :=
  sSup { ((∑ i, a i) - n) | (a : Fin k → ℕ) (_ : (∏ i, (a i) !) ∣ n !) }

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (h: k > 2), 0 < g k n

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) →
    (∀ (k n : ℕ) (h: k > 2), 0 < g k n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) →
    (∀ (k n : ℕ) (h: k > 2), 0 < g k n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) →
    (∀ (k n : ℕ) (h: k > 2), 0 < g k n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) →
    (∀ (k n : ℕ) (h: k > 2), 0 < g k n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) →
    (∀ (k n : ℕ) (h: k > 2), 0 < g k n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) →
    (∀ (k n : ℕ) (h: k > 2), 0 < g k n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) →
    (∀ (k n : ℕ) (h: k > 2), 0 < g k n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (k > 2) := by
  omega

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (k > 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (k > 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (k > 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (k > 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (k > 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (k > 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 2) ↔ (k > 2))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 2) ↔ (k > 2))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 2) ↔ (k > 2))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 2) ↔ (k > 2))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 2) ↔ (k > 2))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 2) ↔ (k > 2))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k > 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k > 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k > 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k > 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k > 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k > 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (h: k ≥ 3), 0 < g k n

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) →
    (∀ (k n : ℕ) (h: k ≥ 3), 0 < g k n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) →
    (∀ (k n : ℕ) (h: k ≥ 3), 0 < g k n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) →
    (∀ (k n : ℕ) (h: k ≥ 3), 0 < g k n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) →
    (∀ (k n : ℕ) (h: k ≥ 3), 0 < g k n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) →
    (∀ (k n : ℕ) (h: k ≥ 3), 0 < g k n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) →
    (∀ (k n : ℕ) (h: k ≥ 3), 0 < g k n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) →
    (∀ (k n : ℕ) (h: k ≥ 3), 0 < g k n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (k ≥ 3) := by
  omega

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (k ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (k ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (k ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (k ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (k ≥ 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (k ≥ 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 2) ↔ (k ≥ 3))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 2) ↔ (k ≥ 3))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 2) ↔ (k ≥ 3))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 2) ↔ (k ≥ 3))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 2) ↔ (k ≥ 3))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 2) ↔ (k ≥ 3))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 2) ↔ (k ≥ 3))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k ≥ 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k ≥ 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k ≥ 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k ≥ 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k ≥ 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k ≥ 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k ≥ 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (h: 2 ≤ k), 0 < g k n

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (k ≥ 2) ↔ (2 ≤ k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (k ≥ 2) ↔ (2 ≤ k) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (k ≥ 2) ↔ (2 ≤ k) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (k ≥ 2) ↔ (2 ≤ k) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (k ≥ 2) ↔ (2 ≤ k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (k ≥ 2) ↔ (2 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (k ≥ 2) ↔ (2 ≤ k) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (k ≥ 2) ↔ (2 ≤ k) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) ↔
    (∀ (k n : ℕ) (h: 2 ≤ k), 0 < g k n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) ↔
    (∀ (k n : ℕ) (h: 2 ≤ k), 0 < g k n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) ↔
    (∀ (k n : ℕ) (h: 2 ≤ k), 0 < g k n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) ↔
    (∀ (k n : ℕ) (h: 2 ≤ k), 0 < g k n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (h: k ≥ 2), g k n > 0

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (0 < g k n) ↔ (g k n > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (0 < g k n) ↔ (g k n > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (0 < g k n) ↔ (g k n > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (0 < g k n) ↔ (g k n > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (0 < g k n) ↔ (g k n > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (0 < g k n) ↔ (g k n > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (0 < g k n) ↔ (g k n > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (0 < g k n) ↔ (g k n > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) ↔
    (∀ (k n : ℕ) (h: k ≥ 2), g k n > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) ↔
    (∀ (k n : ℕ) (h: k ≥ 2), g k n > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) ↔
    (∀ (k n : ℕ) (h: k ≥ 2), g k n > 0) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) ↔
    (∀ (k n : ℕ) (h: k ≥ 2), g k n > 0) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (h₀: k ≥ 2), 0 < g k n

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) ↔
    (∀ (k n : ℕ) (h₀: k ≥ 2), 0 < g k n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) ↔
    (∀ (k n : ℕ) (h₀: k ≥ 2), 0 < g k n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) ↔
    (∀ (k n : ℕ) (h₀: k ≥ 2), 0 < g k n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) ↔
    (∀ (k n : ℕ) (h₀: k ≥ 2), 0 < g k n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (h: ¬(k < 2)), 0 < g k n

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (k ≥ 2) ↔ (¬(k < 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (k ≥ 2) ↔ (¬(k < 2)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (k ≥ 2) ↔ (¬(k < 2)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (k ≥ 2) ↔ (¬(k < 2)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (k ≥ 2) ↔ (¬(k < 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (k ≥ 2) ↔ (¬(k < 2)) := by
  omega

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (k ≥ 2) ↔ (¬(k < 2)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (k ≥ 2) ↔ (¬(k < 2)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) ↔
    (∀ (k n : ℕ) (h: ¬(k < 2)), 0 < g k n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) ↔
    (∀ (k n : ℕ) (h: ¬(k < 2)), 0 < g k n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) ↔
    (∀ (k n : ℕ) (h: ¬(k < 2)), 0 < g k n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) ↔
    (∀ (k n : ℕ) (h: ¬(k < 2)), 0 < g k n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (h: k > 1), 0 < g k n

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (k ≥ 2) ↔ (k > 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (k ≥ 2) ↔ (k > 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (k ≥ 2) ↔ (k > 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (k ≥ 2) ↔ (k > 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (k ≥ 2) ↔ (k > 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (k ≥ 2) ↔ (k > 1) := by
  omega

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (k ≥ 2) ↔ (k > 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k n : ℕ) :
    (k ≥ 2) ↔ (k > 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) ↔
    (∀ (k n : ℕ) (h: k > 1), 0 < g k n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) ↔
    (∀ (k n : ℕ) (h: k > 1), 0 < g k n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) ↔
    (∀ (k n : ℕ) (h: k > 1), 0 < g k n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) ↔
    (∀ (k n : ℕ) (h: k > 1), 0 < g k n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (h: 2 < k), 0 < g k n

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) →
    (∀ (k n : ℕ) (h: 2 < k), 0 < g k n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) →
    (∀ (k n : ℕ) (h: 2 < k), 0 < g k n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) →
    (∀ (k n : ℕ) (h: 2 < k), 0 < g k n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) →
    (∀ (k n : ℕ) (h: 2 < k), 0 < g k n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) →
    (∀ (k n : ℕ) (h: 2 < k), 0 < g k n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) →
    (∀ (k n : ℕ) (h: 2 < k), 0 < g k n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) →
    (∀ (k n : ℕ) (h: 2 < k), 0 < g k n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (2 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (2 < k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (2 < k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (2 < k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (2 < k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (2 < k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (2 < k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 2) ↔ (2 < k))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 2) ↔ (2 < k))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 2) ↔ (2 < k))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 2) ↔ (2 < k))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 2) ↔ (2 < k))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 2) ↔ (2 < k))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (2 < k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (2 < k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (2 < k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (2 < k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (2 < k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (2 < k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (h: 3 ≤ k), 0 < g k n

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) →
    (∀ (k n : ℕ) (h: 3 ≤ k), 0 < g k n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) →
    (∀ (k n : ℕ) (h: 3 ≤ k), 0 < g k n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) →
    (∀ (k n : ℕ) (h: 3 ≤ k), 0 < g k n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) →
    (∀ (k n : ℕ) (h: 3 ≤ k), 0 < g k n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) →
    (∀ (k n : ℕ) (h: 3 ≤ k), 0 < g k n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) →
    (∀ (k n : ℕ) (h: 3 ≤ k), 0 < g k n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) →
    (∀ (k n : ℕ) (h: 3 ≤ k), 0 < g k n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (3 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (3 ≤ k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (3 ≤ k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 2) ↔ (3 ≤ k))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 2) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 2) ↔ (3 ≤ k))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 2) ↔ (3 ≤ k))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 2) ↔ (3 ≤ k))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 2) ↔ (3 ≤ k))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 2) ↔ (3 ≤ k))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (3 ≤ k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (3 ≤ k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (3 ≤ k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (3 ≤ k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (3 ≤ k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (3 ≤ k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (3 ≤ k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (h: k > 2), g k n > 0

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) →
    (∀ (k n : ℕ) (h: k > 2), g k n > 0) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) →
    (∀ (k n : ℕ) (h: k > 2), g k n > 0) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) →
    (∀ (k n : ℕ) (h: k > 2), g k n > 0) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) →
    (∀ (k n : ℕ) (h: k > 2), g k n > 0) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) →
    (∀ (k n : ℕ) (h: k > 2), g k n > 0) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) →
    (∀ (k n : ℕ) (h: k > 2), g k n > 0) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) →
    (∀ (k n : ℕ) (h: k > 2), g k n > 0) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (k > 2) := by
  omega

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (k > 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (k > 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (k > 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (k > 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (k > 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (k > 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 2) ↔ (k > 2))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 2) ↔ (k > 2))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 2) ↔ (k > 2))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 2) ↔ (k > 2))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 2) ↔ (k > 2))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 2) ↔ (k > 2))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k > 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k > 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k > 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k > 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k > 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k > 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (h: k ≥ 3), g k n > 0

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) →
    (∀ (k n : ℕ) (h: k ≥ 3), g k n > 0) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) →
    (∀ (k n : ℕ) (h: k ≥ 3), g k n > 0) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) →
    (∀ (k n : ℕ) (h: k ≥ 3), g k n > 0) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) →
    (∀ (k n : ℕ) (h: k ≥ 3), g k n > 0) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) →
    (∀ (k n : ℕ) (h: k ≥ 3), g k n > 0) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) →
    (∀ (k n : ℕ) (h: k ≥ 3), g k n > 0) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) →
    (∀ (k n : ℕ) (h: k ≥ 3), g k n > 0) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (k ≥ 3) := by
  omega

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (k ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (k ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (k ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (k ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (k ≥ 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (k ≥ 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 2) ↔ (k ≥ 3))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 2) ↔ (k ≥ 3))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 2) ↔ (k ≥ 3))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 2) ↔ (k ≥ 3))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 2) ↔ (k ≥ 3))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 2) ↔ (k ≥ 3))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 2) ↔ (k ≥ 3))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k ≥ 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k ≥ 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k ≥ 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k ≥ 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k ≥ 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k ≥ 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k ≥ 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (h: k ≥ 1), 0 < g k n

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 1), 0 < g k n) →
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 1), 0 < g k n) →
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 1), 0 < g k n) →
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 1), 0 < g k n) →
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 1), 0 < g k n) →
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 1), 0 < g k n) →
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (h: k ≥ 1), 0 < g k n) →
    (∀ (k n : ℕ) (h: k ≥ 2), 0 < g k n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (k ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (k ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (k ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (k ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (k ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (k ≥ 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k n : ℕ)  :
    (k ≥ 2) ↔ (k ≥ 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 2) ↔ (k ≥ 1))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 2) ↔ (k ≥ 1))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 2) ↔ (k ≥ 1))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 2) ↔ (k ≥ 1))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 2) ↔ (k ≥ 1))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 2) ↔ (k ≥ 1))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k ≥ 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k ≥ 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k ≥ 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k ≥ 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k ≥ 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 2) ↔ (k ≥ 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (k n : ℕ) (h: k ≥ 2) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (k n : ℕ) (h: k ≥ 2) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (k n : ℕ) (h: k ≥ 2) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (k n : ℕ) (h: k ≥ 2) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (k n : ℕ) (h: k ≥ 2) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
