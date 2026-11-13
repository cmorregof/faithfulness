import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 358

*References:*
- [erdosproblems.com/358](https://www.erdosproblems.com/358)
- [Ta26] T. Tao, [Erdős problem 358](https://terrytao.wordpress.com/wp-content/uploads/2026/02/erdos-358-2.pdf) (2026)
-/

section

namespace Erdos358

open Filter Finset

/-
Let $a$ be an infinite sequence of integers. `intervalRepresentations A n` is the set of solutions
to $$n=\sum_{u\leq i\leq v}a_i.$$ where `u` and `v` are positive integers.
-/
def intervalRepresentations (A : ℕ → ℕ) (n : ℕ) : Set (ℕ × ℕ) :=
  {(u, v) | 0 < u ∧ 0 < v ∧ n = ∑ i ∈ Icc u v, A i}

/-
Let $a$ be an infinite sequence of integers. Let $f(n)$ count the number of
solutions to $$n=\sum_{u\leq i\leq v}a_i.$$
-/
noncomputable def f (A : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.card (intervalRepresentations A n)

/-
Let $a$ be an infinite sequence of integers. `intervalRepresentationsNonTrivial A n` is the set of
solutions to $$n=\sum_{u\leq i\leq v}a_i$$ such that the sum has at least two terms.
-/
def intervalRepresentationsNonTrivial (A : ℕ → ℕ) (n : ℕ) : Set (ℕ × ℕ) :=
  {(u, v) | 0 < u ∧ 0 < v ∧ u < v ∧ n = ∑ i ∈ Icc u v, A i}

/-
Let $a$ be an infinite sequence of integers. Let $g(n)$ count the number of
solutions to $$n=\sum_{u\leq i\leq v}a_i.$$ such that the sum has at least two terms.
-/
noncomputable def g (A : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.card (intervalRepresentationsNonTrivial A n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hf : 2 ≤ f A n), 1 ≤ g A n

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hf : 2 ≤ f A n) :
    (0 < n) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hf : 2 ≤ f A n) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hf : 2 ≤ f A n) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hf : 2 ≤ f A n) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hf : 2 ≤ f A n) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hf : 2 ≤ f A n) :
    (0 < n) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hf : 2 ≤ f A n) :
    (0 < n) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 < g A n

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 < g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 < g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 < g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 < g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 < g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 < g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 < g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 < f A n), 1 ≤ g A n

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 < f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 < f A n), 1 ≤ g A n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 < f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 < f A n), 1 ≤ g A n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 < f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 < f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 < f A n), 1 ≤ g A n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hn : 0 < n) :
    (2 ≤ f A n) ↔ (2 < f A n) := by
  omega

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hn : 0 < n) :
    (2 ≤ f A n) ↔ (2 < f A n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hn : 0 < n) :
    (2 ≤ f A n) ↔ (2 < f A n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hn : 0 < n) :
    (2 ≤ f A n) ↔ (2 < f A n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hn : 0 < n) :
    (2 ≤ f A n) ↔ (2 < f A n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hn : 0 < n) :
    (2 ≤ f A n) ↔ (2 < f A n) := by
  simp_all

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hn : 0 < n) :
    (2 ≤ f A n) ↔ (2 < f A n) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≥ g A n

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≥ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≥ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≥ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≥ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≥ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≥ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≥ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≥ g A n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≥ g A n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≥ g A n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≥ g A n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≥ g A n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≥ g A n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≥ g A n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : n > 0) (hf : 2 ≤ f A n), 1 ≤ g A n

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} :
    (0 < n) ↔ (n > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} :
    (0 < n) ↔ (n > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} :
    (0 < n) ↔ (n > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} :
    (0 < n) ↔ (n > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} :
    (0 < n) ↔ (n > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} :
    (0 < n) ↔ (n > 0) := by
  omega

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} :
    (0 < n) ↔ (n > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} :
    (0 < n) ↔ (n > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) ↔
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : n > 0) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) ↔
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : n > 0) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) ↔
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : n > 0) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) ↔
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : n > 0) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), g A n ≥ 1

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} :
    (1 ≤ g A n) ↔ (g A n ≥ 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} :
    (1 ≤ g A n) ↔ (g A n ≥ 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} :
    (1 ≤ g A n) ↔ (g A n ≥ 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} :
    (1 ≤ g A n) ↔ (g A n ≥ 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} :
    (1 ≤ g A n) ↔ (g A n ≥ 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} :
    (1 ≤ g A n) ↔ (g A n ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} :
    (1 ≤ g A n) ↔ (g A n ≥ 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} :
    (1 ≤ g A n) ↔ (g A n ≥ 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) ↔
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), g A n ≥ 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) ↔
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), g A n ≥ 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) ↔
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), g A n ≥ 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) ↔
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), g A n ≥ 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hf : 2 ≤ f A n) (hn : 0 < n), 1 ≤ g A n

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) ↔
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hf : 2 ≤ f A n) (hn : 0 < n), 1 ≤ g A n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) ↔
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hf : 2 ≤ f A n) (hn : 0 < n), 1 ≤ g A n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) ↔
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hf : 2 ≤ f A n) (hn : 0 < n), 1 ≤ g A n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) ↔
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hf : 2 ≤ f A n) (hn : 0 < n), 1 ≤ g A n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℕ → ℕ} (hA₀ : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) ↔
    (∀ {A : ℕ → ℕ} (hA₀ : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) ↔
    (∀ {A : ℕ → ℕ} (hA₀ : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) ↔
    (∀ {A : ℕ → ℕ} (hA₀ : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) ↔
    (∀ {A : ℕ → ℕ} (hA₀ : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : ¬(n ≤ 0)) (hf : 2 ≤ f A n), 1 ≤ g A n

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) ↔
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : ¬(n ≤ 0)) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) ↔
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : ¬(n ≤ 0)) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) ↔
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : ¬(n ≤ 0)) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) ↔
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : ¬(n ≤ 0)) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 1 ≤ n) (hf : 2 ≤ f A n), 1 ≤ g A n

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} :
    (0 < n) ↔ (1 ≤ n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} :
    (0 < n) ↔ (1 ≤ n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} :
    (0 < n) ↔ (1 ≤ n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} :
    (0 < n) ↔ (1 ≤ n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} :
    (0 < n) ↔ (1 ≤ n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} :
    (0 < n) ↔ (1 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} :
    (0 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} :
    (0 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) ↔
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 1 ≤ n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) ↔
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 1 ≤ n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) ↔
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 1 ≤ n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) ↔
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 1 ≤ n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : n > 0) (hf : 2 ≤ f A n), 1 < g A n

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : n > 0) (hf : 2 ≤ f A n), 1 < g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : n > 0) (hf : 2 ≤ f A n), 1 < g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : n > 0) (hf : 2 ≤ f A n), 1 < g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : n > 0) (hf : 2 ≤ f A n), 1 < g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : n > 0) (hf : 2 ≤ f A n), 1 < g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : n > 0) (hf : 2 ≤ f A n), 1 < g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : n > 0) (hf : 2 ≤ f A n), 1 < g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : n > 0) (hf : 2 < f A n), 1 ≤ g A n

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : n > 0) (hf : 2 < f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : n > 0) (hf : 2 < f A n), 1 ≤ g A n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : n > 0) (hf : 2 < f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : n > 0) (hf : 2 < f A n), 1 ≤ g A n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : n > 0) (hf : 2 < f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : n > 0) (hf : 2 < f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : n > 0) (hf : 2 < f A n), 1 ≤ g A n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hn : 0 < n) :
    (2 ≤ f A n) ↔ (2 < f A n) := by
  omega

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hn : 0 < n) :
    (2 ≤ f A n) ↔ (2 < f A n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hn : 0 < n) :
    (2 ≤ f A n) ↔ (2 < f A n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hn : 0 < n) :
    (2 ≤ f A n) ↔ (2 < f A n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hn : 0 < n) :
    (2 ≤ f A n) ↔ (2 < f A n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hn : 0 < n) :
    (2 ≤ f A n) ↔ (2 < f A n) := by
  simp_all

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hn : 0 < n) :
    (2 ≤ f A n) ↔ (2 < f A n) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : n > 0) (hf : 2 ≤ f A n), 1 ≥ g A n

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : n > 0) (hf : 2 ≤ f A n), 1 ≥ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : n > 0) (hf : 2 ≤ f A n), 1 ≥ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : n > 0) (hf : 2 ≤ f A n), 1 ≥ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : n > 0) (hf : 2 ≤ f A n), 1 ≥ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : n > 0) (hf : 2 ≤ f A n), 1 ≥ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : n > 0) (hf : 2 ≤ f A n), 1 ≥ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : n > 0) (hf : 2 ≤ f A n), 1 ≥ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : n > 0) (hf : 2 ≤ f A n), 1 ≥ g A n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : n > 0) (hf : 2 ≤ f A n), 1 ≥ g A n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : n > 0) (hf : 2 ≤ f A n), 1 ≥ g A n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : n > 0) (hf : 2 ≤ f A n), 1 ≥ g A n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : n > 0) (hf : 2 ≤ f A n), 1 ≥ g A n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : n > 0) (hf : 2 ≤ f A n), 1 ≥ g A n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : n > 0) (hf : 2 ≤ f A n), 1 ≥ g A n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), g A n > 1

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), g A n > 1) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), g A n > 1) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), g A n > 1) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), g A n > 1) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), g A n > 1) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), g A n > 1) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), g A n > 1) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 < f A n), g A n ≥ 1

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 < f A n), g A n ≥ 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 < f A n), g A n ≥ 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 < f A n), g A n ≥ 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 < f A n), g A n ≥ 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 < f A n), g A n ≥ 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 < f A n), g A n ≥ 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 < f A n), g A n ≥ 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hn : 0 < n) :
    (2 ≤ f A n) ↔ (2 < f A n) := by
  omega

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hn : 0 < n) :
    (2 ≤ f A n) ↔ (2 < f A n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hn : 0 < n) :
    (2 ≤ f A n) ↔ (2 < f A n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hn : 0 < n) :
    (2 ≤ f A n) ↔ (2 < f A n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hn : 0 < n) :
    (2 ≤ f A n) ↔ (2 < f A n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hn : 0 < n) :
    (2 ≤ f A n) ↔ (2 < f A n) := by
  simp_all

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hn : 0 < n) :
    (2 ≤ f A n) ↔ (2 < f A n) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), g A n ≤ 1

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), g A n ≤ 1) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), g A n ≤ 1) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), g A n ≤ 1) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), g A n ≤ 1) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), g A n ≤ 1) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), g A n ≤ 1) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), g A n ≤ 1) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), g A n ≤ 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), g A n ≤ 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), g A n ≤ 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), g A n ≤ 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), g A n ≤ 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), g A n ≤ 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), g A n ≤ 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 1 ≤ n) (hf : 2 ≤ f A n), 1 < g A n

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 1 ≤ n) (hf : 2 ≤ f A n), 1 < g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 1 ≤ n) (hf : 2 ≤ f A n), 1 < g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 1 ≤ n) (hf : 2 ≤ f A n), 1 < g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 1 ≤ n) (hf : 2 ≤ f A n), 1 < g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 1 ≤ n) (hf : 2 ≤ f A n), 1 < g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 1 ≤ n) (hf : 2 ≤ f A n), 1 < g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 1 ≤ n) (hf : 2 ≤ f A n), 1 < g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 1 < n) (hf : 2 ≤ f A n), 1 ≤ g A n

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 1 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 1 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 1 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 1 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 1 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 1 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 1 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hf : 2 ≤ f A n) :
    (0 < n) ↔ (1 < n) := by
  omega

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hf : 2 ≤ f A n) :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hf : 2 ≤ f A n) :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hf : 2 ≤ f A n) :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hf : 2 ≤ f A n) :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hf : 2 ≤ f A n) :
    (0 < n) ↔ (1 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hf : 2 ≤ f A n) :
    (0 < n) ↔ (1 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 1 ≤ n) (hf : 2 ≤ f A n), 1 ≥ g A n

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 1 ≤ n) (hf : 2 ≤ f A n), 1 ≥ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 1 ≤ n) (hf : 2 ≤ f A n), 1 ≥ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 1 ≤ n) (hf : 2 ≤ f A n), 1 ≥ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 1 ≤ n) (hf : 2 ≤ f A n), 1 ≥ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 1 ≤ n) (hf : 2 ≤ f A n), 1 ≥ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 1 ≤ n) (hf : 2 ≤ f A n), 1 ≥ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 1 ≤ n) (hf : 2 ≤ f A n), 1 ≥ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 1 ≤ n) (hf : 2 ≤ f A n), 1 ≥ g A n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 1 ≤ n) (hf : 2 ≤ f A n), 1 ≥ g A n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 1 ≤ n) (hf : 2 ≤ f A n), 1 ≥ g A n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 1 ≤ n) (hf : 2 ≤ f A n), 1 ≥ g A n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 1 ≤ n) (hf : 2 ≤ f A n), 1 ≥ g A n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 1 ≤ n) (hf : 2 ≤ f A n), 1 ≥ g A n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 1 ≤ n) (hf : 2 ≤ f A n), 1 ≥ g A n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n), 1 ≤ g A n

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n), 1 ≤ g A n) →
    (∀ {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n) (hf : 2 ≤ f A n), 1 ≤ g A n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hn : 0 < n) :
    (2 ≤ f A n) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hn : 0 < n) :
    (2 ≤ f A n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hn : 0 < n) :
    (2 ≤ f A n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hn : 0 < n) :
    (2 ≤ f A n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hn : 0 < n) :
    (2 ≤ f A n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hn : 0 < n) :
    (2 ≤ f A n) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hn : 0 < n) :
    (2 ≤ f A n) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hn : 0 < n) (hf : 2 ≤ f A n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hn : 0 < n) (hf : 2 ≤ f A n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hn : 0 < n) (hf : 2 ≤ f A n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hn : 0 < n) (hf : 2 ≤ f A n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {A : ℕ → ℕ} {n : ℕ} (hA : StrictMono A) (hn : 0 < n) (hf : 2 ≤ f A n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
