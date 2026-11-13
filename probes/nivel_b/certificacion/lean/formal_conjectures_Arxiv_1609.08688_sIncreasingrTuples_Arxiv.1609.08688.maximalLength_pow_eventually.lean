import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# The length of an $s$-increasing sequence of $r$-tuples

This file contains the formalisation of [GoLo21] up to and
including Conjecture 1.8.

*References:*
- [arxiv/1609.08688](https://arxiv.org/abs/1609.08688)
  **The length of an $s$-increasing sequence of $r$-tuples** by *W. T. Gowers, J. Long*
- [GoLo21](https://www.cambridge.org/core/journals/combinatorics-probability-and-computing/article/abs/length-of-an-sincreasing-sequence-of-rtuples/7301418D47DB1ECD6BE71C20E8A98D0A)
  **The length of an $s$-increasing sequence of $r$-tuples**
  by *W. T. Gowers, J. Long*, Combinatorics, Probability and Computing (2021), 686-721
-/

section

namespace Arxiv.«1609.08688»

/--
Let $a = (a_1, a_2, a_3)$ and $b = (b_1, b_2, b_3)$ be two triples of integers.
Say that $a$ is $2$-less than $b$, or $a <_2 b$, if $a_i < b_i$ for at least
two coordinates $i$.
-/
def lt₂ {α : Type*} [LT α] (a b : Fin 3 → α) : Prop :=
  ∃ (i j : Fin 3), i ≠ j ∧ a i < b i ∧ a j < b j

local infix:50 " <₂ " => lt₂

/--
Since the $2$-less relation is not transitive, we make a further definition to
specify transivity.
-/
def IsIncreasing₂ {α : Type*} [LT α] (s : List (Fin 3 → α)) : Prop := s.Pairwise lt₂

/--
Let $F(n)$ be the maximal length of a $2$-increasing sequence of triples with each coordinate
belong to $[n]$ ($= \{1, 2, ..., n\}$).
-/
noncomputable def maximalLength (n : ℕ) : ℕ :=
  sSup { List.length s | (s) (_ : ∀ a ∈ s, Set.range a ⊆ Set.Icc 1 n) (_ : IsIncreasing₂ s) }

local notation "F" => maximalLength

/-- Two triples $t_1$ and $t_2$ are $2$-comparable if one of them is $2$-less
than the other. -/
def IsComparable₂ {α : Type*} [LT α] (t₁ t₂ : Fin 3 → α) : Prop :=
  t₁ <₂ t₂ ∨ t₂ <₂ t₁

/-- A set of triples is $2$-comparable if any two distinct members of it are $2$-comparable. -/
def IsComparableSet₂ {α : Type*} [LT α] (s : List (Fin 3 → α)) : Prop :=
  ∀ t₁ ∈ s, ∀ t₂ ∈ s, t₁ ≠ t₂ → IsComparable₂ t₁ t₂

/-- We define the product of two triples $(a, b, c)$ and $(d, e, f)$ by
$((a, d), (b, e), (c, f))$, where the pairs are ordered lexicographically. -/
def tripleProduct {α : Type*} (a b : Fin 3 → α) : Fin 3 → α ×ₗ α :=
  fun i => toLex (a i, b i)

/-- We define the product $\otimes$ of two sequences $(a_i, b_i, c_i)$ and
$(d_i, e_i, f_i)$ by the sequence $((a_i, d_j), (b_i, e_j), (c_i, f_j))$, where
the indices $(i, j)$ are arranged lexicographically, and the pairs are also
ordered lexicographically. -/
def sequenceProduct {α : Type*} (s t : List (Fin 3 → α)) : List (Fin 3 → α ×ₗ α) :=
  s.flatMap (fun a => List.map (tripleProduct a) t)

local infix:100 " ⊗₂ " => sequenceProduct

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℕ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℕ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℕ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(0 : ℕ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℕ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℕ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℕ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(0 : ℕ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(0 : ℕ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(2 : ℕ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℕ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℕ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℕ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℕ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(0 : ℕ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(0 : ℕ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(0 : ℕ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(2 : ℕ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(2 : ℕ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(3 : ℕ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℕ), (1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℕ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℕ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℕ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℕ), (1/2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(0 : ℕ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(0 : ℕ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(0 : ℕ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(0 : ℕ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(2 : ℕ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(2 : ℕ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(2 : ℕ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔ (∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔ (∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔ (∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔ (∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔ (∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔ (∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℕ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℕ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℕ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(0 : ℕ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℕ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℕ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℕ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(0 : ℕ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(0 : ℕ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(2 : ℕ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℕ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℕ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℕ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℕ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(0 : ℕ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(0 : ℕ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(0 : ℕ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(2 : ℕ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(2 : ℕ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(3 : ℕ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℕ), (1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℕ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℕ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℕ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℕ), (1/2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(0 : ℕ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(0 : ℕ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(0 : ℕ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(0 : ℕ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(2 : ℕ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(2 : ℕ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(2 : ℕ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔ (∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔ (∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔ (∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔ (∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔ (∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔ (∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {e : ℝ} (hn : n > 1) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m

set_option maxHeartbeats 200000 in
example {n : ℕ} {e : ℝ} {b : ℝ} :
    (1 < n) ↔ (n > 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} {e : ℝ} {b : ℝ} :
    (1 < n) ↔ (n > 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} {e : ℝ} {b : ℝ} :
    (1 < n) ↔ (n > 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} {e : ℝ} {b : ℝ} :
    (1 < n) ↔ (n > 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} {e : ℝ} {b : ℝ} :
    (1 < n) ↔ (n > 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} {e : ℝ} {b : ℝ} :
    (1 < n) ↔ (n > 1) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} {e : ℝ} {b : ℝ} :
    (1 < n) ↔ (n > 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} {e : ℝ} {b : ℝ} :
    (1 < n) ↔ (n > 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔
    (∀ {n : ℕ} {e : ℝ} (hn : n > 1) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔
    (∀ {n : ℕ} {e : ℝ} (hn : n > 1) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔
    (∀ {n : ℕ} {e : ℝ} (hn : n > 1) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔
    (∀ {n : ℕ} {e : ℝ} (hn : n > 1) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {e : ℝ} (h : F n = (n : ℝ) ^ e) (hn : 1 < n) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔
    (∀ {n : ℕ} {e : ℝ} (h : F n = (n : ℝ) ^ e) (hn : 1 < n) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔
    (∀ {n : ℕ} {e : ℝ} (h : F n = (n : ℝ) ^ e) (hn : 1 < n) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔
    (∀ {n : ℕ} {e : ℝ} (h : F n = (n : ℝ) ^ e) (hn : 1 < n) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔
    (∀ {n : ℕ} {e : ℝ} (h : F n = (n : ℝ) ^ e) (hn : 1 < n) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {e : ℝ} (hn₀ : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔
    (∀ {n : ℕ} {e : ℝ} (hn₀ : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔
    (∀ {n : ℕ} {e : ℝ} (hn₀ : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔
    (∀ {n : ℕ} {e : ℝ} (hn₀ : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔
    (∀ {n : ℕ} {e : ℝ} (hn₀ : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {e : ℝ} (hn : ¬(n ≤ 1)) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m

set_option maxHeartbeats 200000 in
example {n : ℕ} {e : ℝ} {b : ℝ} :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} {e : ℝ} {b : ℝ} :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} {e : ℝ} {b : ℝ} :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} {e : ℝ} {b : ℝ} :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} {e : ℝ} {b : ℝ} :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} {e : ℝ} {b : ℝ} :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} {e : ℝ} {b : ℝ} :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} {e : ℝ} {b : ℝ} :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔
    (∀ {n : ℕ} {e : ℝ} (hn : ¬(n ≤ 1)) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔
    (∀ {n : ℕ} {e : ℝ} (hn : ¬(n ≤ 1)) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔
    (∀ {n : ℕ} {e : ℝ} (hn : ¬(n ≤ 1)) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔
    (∀ {n : ℕ} {e : ℝ} (hn : ¬(n ≤ 1)) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {e : ℝ} (hn : 2 ≤ n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m

set_option maxHeartbeats 200000 in
example {n : ℕ} {e : ℝ} {b : ℝ} :
    (1 < n) ↔ (2 ≤ n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} {e : ℝ} {b : ℝ} :
    (1 < n) ↔ (2 ≤ n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} {e : ℝ} {b : ℝ} :
    (1 < n) ↔ (2 ≤ n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} {e : ℝ} {b : ℝ} :
    (1 < n) ↔ (2 ≤ n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} {e : ℝ} {b : ℝ} :
    (1 < n) ↔ (2 ≤ n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} {e : ℝ} {b : ℝ} :
    (1 < n) ↔ (2 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} {e : ℝ} {b : ℝ} :
    (1 < n) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} {e : ℝ} {b : ℝ} :
    (1 < n) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔
    (∀ {n : ℕ} {e : ℝ} (hn : 2 ≤ n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔
    (∀ {n : ℕ} {e : ℝ} (hn : 2 ≤ n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔
    (∀ {n : ℕ} {e : ℝ} (hn : 2 ≤ n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔
    (∀ {n : ℕ} {e : ℝ} (hn : 2 ≤ n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {e : ℝ} (hn : n > 1) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : n > 1) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : n > 1) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : n > 1) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : n > 1) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : n > 1) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : n > 1) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : n > 1) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℕ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℕ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℕ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(0 : ℕ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℕ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℕ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℕ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(0 : ℕ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(0 : ℕ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(2 : ℕ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℕ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℕ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℕ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℕ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(0 : ℕ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(0 : ℕ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(0 : ℕ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(2 : ℕ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(2 : ℕ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(3 : ℕ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℕ), (1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℕ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℕ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℕ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℕ), (1/2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(0 : ℕ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(0 : ℕ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(0 : ℕ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(0 : ℕ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(2 : ℕ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(2 : ℕ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(2 : ℕ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔ (∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔ (∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔ (∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔ (∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔ (∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔ (∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {e : ℝ} (hn : n > 1) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : n > 1) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : n > 1) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : n > 1) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : n > 1) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : n > 1) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : n > 1) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : n > 1) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : n > 1) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : n > 1) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : n > 1) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : n > 1) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : n > 1) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : n > 1) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : n > 1) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℕ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℕ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℕ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(0 : ℕ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℕ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℕ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℕ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(0 : ℕ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(0 : ℕ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(2 : ℕ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℕ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℕ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℕ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℕ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(0 : ℕ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(0 : ℕ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(0 : ℕ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(2 : ℕ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(2 : ℕ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(3 : ℕ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℕ), (1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℕ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℕ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℕ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℕ), (1/2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(0 : ℕ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(0 : ℕ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(0 : ℕ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(0 : ℕ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(2 : ℕ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(2 : ℕ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(2 : ℕ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔ (∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔ (∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔ (∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔ (∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔ (∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔ (∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {e : ℝ} (hn : 2 ≤ n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 2 ≤ n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 2 ≤ n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 2 ≤ n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 2 ≤ n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 2 ≤ n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 2 ≤ n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 2 ≤ n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℕ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℕ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℕ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(0 : ℕ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℕ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℕ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℕ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(0 : ℕ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(0 : ℕ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(2 : ℕ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℕ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℕ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℕ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℕ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(0 : ℕ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(0 : ℕ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(0 : ℕ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(2 : ℕ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(2 : ℕ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(3 : ℕ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℕ), (1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℕ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℕ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℕ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℕ), (1/2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(0 : ℕ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(0 : ℕ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(0 : ℕ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(0 : ℕ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(2 : ℕ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(2 : ℕ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(2 : ℕ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔ (∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔ (∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔ (∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔ (∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔ (∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔ (∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b < F m)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {e : ℝ} (hn : 2 ≤ n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 2 ≤ n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 2 ≤ n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 2 ≤ n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 2 ≤ n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 2 ≤ n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 2 ≤ n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 2 ≤ n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 2 ≤ n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 2 ≤ n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 2 ≤ n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 2 ≤ n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 2 ≤ n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 2 ≤ n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) →
    (∀ {n : ℕ} {e : ℝ} (hn : 2 ≤ n) (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e), ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℕ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℕ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℕ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(0 : ℕ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℕ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℕ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℕ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(0 : ℕ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(0 : ℕ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(2 : ℕ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℕ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℕ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℕ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℕ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(0 : ℕ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(0 : ℕ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(0 : ℕ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(2 : ℕ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(2 : ℕ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(3 : ℕ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℕ), (1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℕ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℕ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℕ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℕ), (1/2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(0 : ℕ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(0 : ℕ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(0 : ℕ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(0 : ℕ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(2 : ℕ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(2 : ℕ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (e : ℝ) (b : ℝ), (1 < n) ∧ (F n = (n : ℝ) ^ e) ∧ (b < e) ∧ (¬(∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(2 : ℕ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔ (∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔ (∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔ (∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔ (∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔ (∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℝ), ¬((∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m) ↔ (∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≥ F m)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {n : ℕ} {e : ℝ} {b : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) (hb : b < e) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {n : ℕ} {e : ℝ} {b : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) (hb : b < e) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} {e : ℝ} {b : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) (hb : b < e) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {n : ℕ} {e : ℝ} {b : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) (hb : b < e) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} {e : ℝ} {b : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) (hb : b < e) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
