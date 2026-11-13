import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 865

*References:*
- [erdosproblems.com/865](https://www.erdosproblems.com/865)
- [CES75] Choi, S. L. G. and Erdős, P. and Szemerédi, E., Some additive and multiplicative problems
  in number theory. Acta Arith. (1975), 37--50.
- [Ci26] R. Cipollini, [A sharp $5/8$ bound for an Erdős–Sós pairwise-sums problem](https://arxiv.org/html/2606.29361)
  (2026).
-/

section

open Finset Filter
open scoped Asymptotics

namespace Erdos865

noncomputable def f (N k : ℕ) : ℕ :=
  sInf {m | ∀ A ⊆ Icc 1 N, A.card ≥ m →
    ∃ S ⊆ A, S.card = k ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x + y ∈ A}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 < k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) →
    (∀ (k : ℕ) (hk : 3 < k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) →
    (∀ (k : ℕ) (hk : 3 < k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) →
    (∀ (k : ℕ) (hk : 3 < k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) →
    (∀ (k : ℕ) (hk : 3 < k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) →
    (∀ (k : ℕ) (hk : 3 < k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) →
    (∀ (k : ℕ) (hk : 3 < k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) →
    (∀ (k : ℕ) (hk : 3 < k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (3 ≤ k) ↔ (3 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (3 ≤ k) ↔ (3 < k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (3 ≤ k) ↔ (3 < k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (3 ≤ k) ↔ (3 < k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (3 ≤ k) ↔ (3 < k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (3 ≤ k) ↔ (3 < k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (3 ≤ k) ↔ (3 < k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((3 ≤ k) ↔ (3 < k))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((3 ≤ k) ↔ (3 < k))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((3 ≤ k) ↔ (3 < k))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((3 ≤ k) ↔ (3 < k))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((3 ≤ k) ↔ (3 < k))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((3 ≤ k) ↔ (3 < k))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((3 ≤ k) ↔ (3 < k))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (3 < k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (3 < k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (3 < k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (3 < k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (3 < k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (3 < k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (3 < k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) →
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) →
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) →
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) →
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) →
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) →
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) →
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (3 ≤ k) ↔ (4 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (3 ≤ k) ↔ (4 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (3 ≤ k) ↔ (4 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (3 ≤ k) ↔ (4 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (3 ≤ k) ↔ (4 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (3 ≤ k) ↔ (4 ≤ k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (3 ≤ k) ↔ (4 ≤ k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((3 ≤ k) ↔ (4 ≤ k))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((3 ≤ k) ↔ (4 ≤ k))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((3 ≤ k) ↔ (4 ≤ k))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((3 ≤ k) ↔ (4 ≤ k))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((3 ≤ k) ↔ (4 ≤ k))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((3 ≤ k) ↔ (4 ≤ k))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((3 ≤ k) ↔ (4 ≤ k))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (4 ≤ k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (4 ≤ k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (4 ≤ k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (4 ≤ k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (4 ≤ k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (4 ≤ k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (4 ≤ k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 3), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (k ≥ 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (k ≥ 3) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (k ≥ 3) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (k ≥ 3) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (k ≥ 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (k ≥ 3) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (k ≥ 3) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (k ≥ 3) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) ↔
    (∀ (k : ℕ) (hk : k ≥ 3), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) ↔
    (∀ (k : ℕ) (hk : k ≥ 3), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) ↔
    (∀ (k : ℕ) (hk : k ≥ 3), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) ↔
    (∀ (k : ℕ) (hk : k ≥ 3), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε₁ > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε₁) * N

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) ↔ (∃ ε₁ > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε₁) * N) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) ↔ (∃ ε₁ > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε₁) * N) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) ↔ (∃ ε₁ > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε₁) * N) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) ↔ (∃ ε₁ > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε₁) * N) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) ↔ (∃ ε₁ > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε₁) * N) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) ↔ (∃ ε₁ > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε₁) * N) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) ↔ (∃ ε₁ > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε₁) * N) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) ↔ (∃ ε₁ > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε₁) * N) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) ↔
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε₁ > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε₁) * N) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) ↔
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε₁ > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε₁) * N) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) ↔
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε₁ > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε₁) * N) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) ↔
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε₁ > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε₁) * N) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk₀ : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) ↔
    (∀ (k : ℕ) (hk₀ : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) ↔
    (∀ (k : ℕ) (hk₀ : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) ↔
    (∀ (k : ℕ) (hk₀ : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) ↔
    (∀ (k : ℕ) (hk₀ : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : ¬(k < 3)), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (¬(k < 3)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (¬(k < 3)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (¬(k < 3)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (¬(k < 3)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (¬(k < 3)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (¬(k < 3)) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (¬(k < 3)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (¬(k < 3)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) ↔
    (∀ (k : ℕ) (hk : ¬(k < 3)), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) ↔
    (∀ (k : ℕ) (hk : ¬(k < 3)), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) ↔
    (∀ (k : ℕ) (hk : ¬(k < 3)), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) ↔
    (∀ (k : ℕ) (hk : ¬(k < 3)), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 < k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (2 < k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (2 < k) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (2 < k) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (2 < k) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (2 < k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (2 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (2 < k) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (2 < k) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) ↔
    (∀ (k : ℕ) (hk : 2 < k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) ↔
    (∀ (k : ℕ) (hk : 2 < k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) ↔
    (∀ (k : ℕ) (hk : 2 < k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) ↔
    (∀ (k : ℕ) (hk : 2 < k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k > 3), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) →
    (∀ (k : ℕ) (hk : k > 3), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) →
    (∀ (k : ℕ) (hk : k > 3), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) →
    (∀ (k : ℕ) (hk : k > 3), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) →
    (∀ (k : ℕ) (hk : k > 3), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) →
    (∀ (k : ℕ) (hk : k > 3), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) →
    (∀ (k : ℕ) (hk : k > 3), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) →
    (∀ (k : ℕ) (hk : k > 3), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (3 ≤ k) ↔ (k > 3) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (3 ≤ k) ↔ (k > 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (3 ≤ k) ↔ (k > 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (3 ≤ k) ↔ (k > 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (3 ≤ k) ↔ (k > 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (3 ≤ k) ↔ (k > 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (3 ≤ k) ↔ (k > 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((3 ≤ k) ↔ (k > 3))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((3 ≤ k) ↔ (k > 3))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((3 ≤ k) ↔ (k > 3))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((3 ≤ k) ↔ (k > 3))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((3 ≤ k) ↔ (k > 3))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((3 ≤ k) ↔ (k > 3))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((3 ≤ k) ↔ (k > 3))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (k > 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (k > 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (k > 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (k > 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (k > 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (k > 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (k > 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 4), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) →
    (∀ (k : ℕ) (hk : k ≥ 4), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) →
    (∀ (k : ℕ) (hk : k ≥ 4), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) →
    (∀ (k : ℕ) (hk : k ≥ 4), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) →
    (∀ (k : ℕ) (hk : k ≥ 4), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) →
    (∀ (k : ℕ) (hk : k ≥ 4), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) →
    (∀ (k : ℕ) (hk : k ≥ 4), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) →
    (∀ (k : ℕ) (hk : k ≥ 4), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (3 ≤ k) ↔ (k ≥ 4) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (3 ≤ k) ↔ (k ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (3 ≤ k) ↔ (k ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (3 ≤ k) ↔ (k ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (3 ≤ k) ↔ (k ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (3 ≤ k) ↔ (k ≥ 4) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (3 ≤ k) ↔ (k ≥ 4) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((3 ≤ k) ↔ (k ≥ 4))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((3 ≤ k) ↔ (k ≥ 4))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((3 ≤ k) ↔ (k ≥ 4))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((3 ≤ k) ↔ (k ≥ 4))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((3 ≤ k) ↔ (k ≥ 4))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((3 ≤ k) ↔ (k ≥ 4))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((3 ≤ k) ↔ (k ≥ 4))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (k ≥ 4)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (k ≥ 4)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (k ≥ 4)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (k ≥ 4)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (k ≥ 4)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (k ≥ 4)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (k ≥ 4)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) →
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) →
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) →
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) →
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) →
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) →
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) →
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ ε > 0, ∀ᶠ N in atTop, (f N k : ℝ) ≤ (2 / 3 - ε) * N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (3 ≤ k) ↔ (2 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (3 ≤ k) ↔ (2 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (3 ≤ k) ↔ (2 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (3 ≤ k) ↔ (2 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (3 ≤ k) ↔ (2 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (3 ≤ k) ↔ (2 ≤ k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (3 ≤ k) ↔ (2 ≤ k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((3 ≤ k) ↔ (2 ≤ k))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((3 ≤ k) ↔ (2 ≤ k))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((3 ≤ k) ↔ (2 ≤ k))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((3 ≤ k) ↔ (2 ≤ k))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((3 ≤ k) ↔ (2 ≤ k))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((3 ≤ k) ↔ (2 ≤ k))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((3 ≤ k) ↔ (2 ≤ k))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (2 ≤ k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (2 ≤ k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (2 ≤ k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (2 ≤ k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (2 ≤ k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (2 ≤ k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((3 ≤ k) ↔ (2 ≤ k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 3 ≤ k) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 3 ≤ k) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 3 ≤ k) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 3 ≤ k) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 3 ≤ k) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
