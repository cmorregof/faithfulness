import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 841

*References:*
- [erdosproblems.com/841](https://www.erdosproblems.com/841)
- [ErSe92] Erdős, Paul and Selfridge, J. L., Problems and Solutions: Solutions: 6655. Amer. Math.
  Monthly (1992), 791--794.
- [BPZ24] Bui, Hung M. and Pratt, Kyle and Zaharescu, Alexandru, A problem of
  Erdős-Graham-Granville-Selfridge on integral points on hyperelliptic curves. Math. Proc.
  Cambridge Philos. Soc. (2024), 309--323.
- [Gu04] Guy, Richard K., Unsolved problems in number theory. (2004), xviii+437.
-/

section

open Filter Real Topology

namespace Erdos841

/-- `t n` is the least `T` such that `{n + 1, …, n + T}` contains a subset whose product with `n`
is a square; `t n = 0` if and only if `n` is itself a square. -/
noncomputable def t (n : ℕ) : ℕ :=
  sInf {T | ∃ J ⊆ Finset.Icc 1 T, IsSquare (n * ∏ j ∈ J, (n + j))}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)) :
    (1 < n) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)) :
    (1 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)) :
    (1 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)) :
    (1 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)) :
    (1 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)) :
    (1 < n) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)) :
    (1 < n) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ∧ (¬((1 < n) ↔ (True))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ∧ (¬((1 < n) ↔ (True))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ∧ (¬((1 < n) ↔ (True))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ∧ (¬((1 < n) ↔ (True))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ∧ (¬((1 < n) ↔ (True))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ∧ (¬((1 < n) ↔ (True))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)) :
    (1 < n) ↔ (1 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)) :
    (1 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)) :
    (1 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)) :
    (1 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)) :
    (1 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)) :
    (1 < n) ↔ (1 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)) :
    (1 < n) ↔ (1 ≤ n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ∧ (¬((1 < n) ↔ (1 ≤ n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ∧ (¬((1 < n) ↔ (1 ≤ n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ∧ (¬((1 < n) ↔ (1 ≤ n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ∧ (¬((1 < n) ↔ (1 ≤ n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ∧ (¬((1 < n) ↔ (1 ≤ n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ∧ (¬((1 < n) ↔ (1 ≤ n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (1 ≤ n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (1 ≤ n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (1 ≤ n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (1 ≤ n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (1 ≤ n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (1 ≤ n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n) (h : √(3 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(3 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(3 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(3 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(3 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(3 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(3 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(3 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(3 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(3 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(3 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(3 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(3 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(3 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(3 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 < n) :
    (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(3 * n) + 1 < (n.maxPrimeFac : ℝ)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 < n) :
    (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(3 * n) + 1 < (n.maxPrimeFac : ℝ)) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 < n) :
    (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(3 * n) + 1 < (n.maxPrimeFac : ℝ)) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 < n) :
    (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(3 * n) + 1 < (n.maxPrimeFac : ℝ)) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 < n) :
    (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(3 * n) + 1 < (n.maxPrimeFac : ℝ)) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 < n) :
    (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(3 * n) + 1 < (n.maxPrimeFac : ℝ)) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 < n) :
    (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(3 * n) + 1 < (n.maxPrimeFac : ℝ)) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(3 * n) + 1 < (n.maxPrimeFac : ℝ)))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(3 * n) + 1 < (n.maxPrimeFac : ℝ)))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(3 * n) + 1 < (n.maxPrimeFac : ℝ)))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(3 * n) + 1 < (n.maxPrimeFac : ℝ)))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(3 * n) + 1 < (n.maxPrimeFac : ℝ)))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(3 * n) + 1 < (n.maxPrimeFac : ℝ)))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(3 * n) + 1 < (n.maxPrimeFac : ℝ)))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(3 * n) + 1 < (n.maxPrimeFac : ℝ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(3 * n) + 1 < (n.maxPrimeFac : ℝ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(3 * n) + 1 < (n.maxPrimeFac : ℝ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(3 * n) + 1 < (n.maxPrimeFac : ℝ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(3 * n) + 1 < (n.maxPrimeFac : ℝ))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(3 * n) + 1 < (n.maxPrimeFac : ℝ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(3 * n) + 1 < (n.maxPrimeFac : ℝ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 1) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (n > 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (n > 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (n > 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (n > 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (n > 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (n > 1) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (n > 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (n > 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) ↔
    (∀ (n : ℕ) (hn : n > 1) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) ↔
    (∀ (n : ℕ) (hn : n > 1) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) ↔
    (∀ (n : ℕ) (hn : n > 1) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) ↔
    (∀ (n : ℕ) (hn : n > 1) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)) (hn : 1 < n), t n = n.maxPrimeFac

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) ↔
    (∀ (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)) (hn : 1 < n), t n = n.maxPrimeFac) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) ↔
    (∀ (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)) (hn : 1 < n), t n = n.maxPrimeFac) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) ↔
    (∀ (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)) (hn : 1 < n), t n = n.maxPrimeFac) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) ↔
    (∀ (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)) (hn : 1 < n), t n = n.maxPrimeFac) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn₀ : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) ↔
    (∀ (n : ℕ) (hn₀ : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) ↔
    (∀ (n : ℕ) (hn₀ : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) ↔
    (∀ (n : ℕ) (hn₀ : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) ↔
    (∀ (n : ℕ) (hn₀ : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : ¬(n ≤ 1)) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 1)) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 1)) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 1)) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 1)) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (2 ≤ n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (2 ≤ n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (2 ≤ n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (2 ≤ n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (2 ≤ n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (2 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) ↔
    (∀ (n : ℕ) (hn : 2 ≤ n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) ↔
    (∀ (n : ℕ) (hn : 2 ≤ n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) ↔
    (∀ (n : ℕ) (hn : 2 ≤ n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) ↔
    (∀ (n : ℕ) (hn : 2 ≤ n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 1) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)) :
    (1 < n) ↔ (n ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)) :
    (1 < n) ↔ (n ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)) :
    (1 < n) ↔ (n ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)) :
    (1 < n) ↔ (n ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)) :
    (1 < n) ↔ (n ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)) :
    (1 < n) ↔ (n ≥ 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)) :
    (1 < n) ↔ (n ≥ 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ∧ (¬((1 < n) ↔ (n ≥ 1))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ∧ (¬((1 < n) ↔ (n ≥ 1))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ∧ (¬((1 < n) ↔ (n ≥ 1))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ∧ (¬((1 < n) ↔ (n ≥ 1))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ∧ (¬((1 < n) ↔ (n ≥ 1))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ∧ (¬((1 < n) ↔ (n ≥ 1))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (n ≥ 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (n ≥ 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (n ≥ 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (n ≥ 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (n ≥ 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (n ≥ 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 1) (h : √(3 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 1) (h : √(3 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 1) (h : √(3 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 1) (h : √(3 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 1) (h : √(3 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 1) (h : √(3 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 1) (h : √(3 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 1) (h : √(3 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : n > 1) (h : √(3 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : n > 1) (h : √(3 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : n > 1) (h : √(3 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : n > 1) (h : √(3 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : n > 1) (h : √(3 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : n > 1) (h : √(3 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : n > 1) (h : √(3 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 < n) :
    (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(3 * n) + 1 < (n.maxPrimeFac : ℝ)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 < n) :
    (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(3 * n) + 1 < (n.maxPrimeFac : ℝ)) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 < n) :
    (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(3 * n) + 1 < (n.maxPrimeFac : ℝ)) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 < n) :
    (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(3 * n) + 1 < (n.maxPrimeFac : ℝ)) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 < n) :
    (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(3 * n) + 1 < (n.maxPrimeFac : ℝ)) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 < n) :
    (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(3 * n) + 1 < (n.maxPrimeFac : ℝ)) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 < n) :
    (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(3 * n) + 1 < (n.maxPrimeFac : ℝ)) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(3 * n) + 1 < (n.maxPrimeFac : ℝ)))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(3 * n) + 1 < (n.maxPrimeFac : ℝ)))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(3 * n) + 1 < (n.maxPrimeFac : ℝ)))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(3 * n) + 1 < (n.maxPrimeFac : ℝ)))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(3 * n) + 1 < (n.maxPrimeFac : ℝ)))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(3 * n) + 1 < (n.maxPrimeFac : ℝ)))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(3 * n) + 1 < (n.maxPrimeFac : ℝ)))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(3 * n) + 1 < (n.maxPrimeFac : ℝ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(3 * n) + 1 < (n.maxPrimeFac : ℝ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(3 * n) + 1 < (n.maxPrimeFac : ℝ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(3 * n) + 1 < (n.maxPrimeFac : ℝ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(3 * n) + 1 < (n.maxPrimeFac : ℝ))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(3 * n) + 1 < (n.maxPrimeFac : ℝ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(3 * n) + 1 < (n.maxPrimeFac : ℝ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (h : √(2 * n) + 1 ≤ (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n) (h : √(2 * n) + 1 ≤ (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n) (h : √(2 * n) + 1 ≤ (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n) (h : √(2 * n) + 1 ≤ (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n) (h : √(2 * n) + 1 ≤ (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n) (h : √(2 * n) + 1 ≤ (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n) (h : √(2 * n) + 1 ≤ (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n) (h : √(2 * n) + 1 ≤ (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 < n) :
    (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(2 * n) + 1 ≤ (n.maxPrimeFac : ℝ)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 < n) :
    (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(2 * n) + 1 ≤ (n.maxPrimeFac : ℝ)) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 < n) :
    (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(2 * n) + 1 ≤ (n.maxPrimeFac : ℝ)) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 < n) :
    (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(2 * n) + 1 ≤ (n.maxPrimeFac : ℝ)) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 < n) :
    (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(2 * n) + 1 ≤ (n.maxPrimeFac : ℝ)) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 < n) :
    (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(2 * n) + 1 ≤ (n.maxPrimeFac : ℝ)) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 < n) :
    (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(2 * n) + 1 ≤ (n.maxPrimeFac : ℝ)) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(2 * n) + 1 ≤ (n.maxPrimeFac : ℝ)))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(2 * n) + 1 ≤ (n.maxPrimeFac : ℝ)))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(2 * n) + 1 ≤ (n.maxPrimeFac : ℝ)))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(2 * n) + 1 ≤ (n.maxPrimeFac : ℝ)))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(2 * n) + 1 ≤ (n.maxPrimeFac : ℝ)))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(2 * n) + 1 ≤ (n.maxPrimeFac : ℝ)))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(2 * n) + 1 ≤ (n.maxPrimeFac : ℝ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(2 * n) + 1 ≤ (n.maxPrimeFac : ℝ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(2 * n) + 1 ≤ (n.maxPrimeFac : ℝ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(2 * n) + 1 ≤ (n.maxPrimeFac : ℝ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(2 * n) + 1 ≤ (n.maxPrimeFac : ℝ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (√(2 * n) + 1 ≤ (n.maxPrimeFac : ℝ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 2 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 2 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 2 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 2 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 2 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 2 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 2 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)) :
    (1 < n) ↔ (2 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)) :
    (1 < n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)) :
    (1 < n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)) :
    (1 < n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)) :
    (1 < n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)) :
    (1 < n) ↔ (2 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)) :
    (1 < n) ↔ (2 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ∧ (¬((1 < n) ↔ (2 < n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ∧ (¬((1 < n) ↔ (2 < n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ∧ (¬((1 < n) ↔ (2 < n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ∧ (¬((1 < n) ↔ (2 < n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ∧ (¬((1 < n) ↔ (2 < n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ∧ (¬((1 < n) ↔ (2 < n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (2 < n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (2 < n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (2 < n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (2 < n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (2 < n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (2 < n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 3 ≤ n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)) :
    (1 < n) ↔ (3 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)) :
    (1 < n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)) :
    (1 < n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)) :
    (1 < n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)) :
    (1 < n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)) :
    (1 < n) ↔ (3 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)) :
    (1 < n) ↔ (3 ≤ n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ∧ (¬((1 < n) ↔ (3 ≤ n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ∧ (¬((1 < n) ↔ (3 ≤ n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ∧ (¬((1 < n) ↔ (3 ≤ n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ∧ (¬((1 < n) ↔ (3 ≤ n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ∧ (¬((1 < n) ↔ (3 ≤ n))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ∧ (¬((1 < n) ↔ (3 ≤ n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ∧ (¬((1 < n) ↔ (3 ≤ n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (3 ≤ n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (3 ≤ n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (3 ≤ n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (3 ≤ n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (3 ≤ n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (3 ≤ n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (3 ≤ n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n), t n = n.maxPrimeFac

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), t n = n.maxPrimeFac) →
    (∀ (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)), t n = n.maxPrimeFac) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 < n) :
    (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 < n) :
    (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 < n) :
    (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 < n) :
    (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 < n) :
    (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 < n) :
    (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 < n) :
    (√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (True))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (True))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (True))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (True))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (True))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 < n) ∧ (¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (True))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((√(2 * n) + 1 < (n.maxPrimeFac : ℝ)) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 < n) (h : √(2 * n) + 1 < (n.maxPrimeFac : ℝ)) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
