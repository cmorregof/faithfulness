import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Number of parts in the symmetric representation of $\sigma(n)$

Number of parts in the symmetric representation of $\sigma(n)$. $a(n)$ is $1$ plus the number of pairs $(d_k, d_{k+1})$ of consecutive divisors of $n$
such that $d_{k+1}$ is odd and $d_{k+1} \ge 2 d_k$.

The formula used is
$1 + |\{(d_k, d_{k+1}) \in \text{consecutive pairs of divisors of } n \mid
d_{k+1} \text{ is odd and } d_{k+1} \ge 2 d_k\}|$,
which is a known characterization of the sequence.

*References:*
- [A237271](https://oeis.org/A237271)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/

section

namespace OeisA237271

open Nat Finset List

/--
Number of parts in the symmetric representation of $\sigma(n)$. $a(n)$ is $1$ plus the number of pairs $(d_k, d_{k+1})$ of consecutive divisors of $n$
such that $d_{k+1}$ is odd and $d_{k+1} \ge 2 d_k$.

The formula used is
$1 + |\{(d_k, d_{k+1}) \in \text{consecutive pairs of divisors of } n \mid
d_{k+1} \text{ is odd and } d_{k+1} \ge 2 d_k\}|$,
which is a known characterization of the sequence.
-/
def a (n : ℕ) : ℕ :=
  -- Get the list of divisors of n, sorted ascendingly.
  let divs_list : List ℕ := (n.divisors.sort (· ≤ ·))

  -- Get the list of consecutive pairs of divisors: [(d₁, d₂), (d₂, d₃), ...]
  let consecutive_pairs : List (ℕ × ℕ) := List.zip divs_list divs_list.tail

  -- Count the pairs satisfying the condition
  let count : ℕ := consecutive_pairs.countP fun pair =>
    let d_k := pair.fst
    let d_k_succ := pair.snd
    -- The second divisor d_{k+1} must be odd and at least twice the first divisor d_k.
    Odd d_k_succ ∧ d_k_succ ≥ 2 * d_k

  -- The sequence value is 1 + the count
  1 + count
def sortedDivisorsList (n : ℕ) : List ℕ := (n.divisors.sort (· ≤ ·))

/--
Number of maximal contiguous sublists of divisors of n where each adjacent pair (d_k, d_{k+1})
satisfies d_{k+1} <= 2 * d_k.
This is 1 + the number of "jumps" where d_{k+1} > 2 * d_k.
-/
def num2DenseSublists (n : ℕ) : ℕ :=
  let divs_list := sortedDivisorsList n
  let consecutive_pairs : List (ℕ × ℕ) := List.zip divs_list divs_list.tail

  -- A jump/break occurs when d_{k+1} > 2 * d_k
  let num_jumps : ℕ := consecutive_pairs.countP fun pair =>
    let d_k := pair.fst
    let d_k_succ := pair.snd
    d_k_succ > 2 * d_k

  1 + num_jumps

/-- Number of odd divisors of n (A001227). -/
def A001227 (n : ℕ) : ℕ := (n.divisors.filter Odd).card

/-- Number of odd divisors m of n such that there is a divisor d of n with d < m < 2*d (A239657). -/
def A239657 (n : ℕ) : ℕ :=
  (n.divisors.filter fun m => Odd m ∧ ∃ d ∈ n.divisors, d < m ∧ m < 2 * d).card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (3 * n - 1)))

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (3 * n - 1)))) →
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (3 * n - 1)))) →
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (3 * n - 1)))) →
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (3 * n - 1)))) →
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (3 * n - 1)))) →
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (3 * n - 1)))) →
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (3 * n - 1)))) →
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) →
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (3 * n - 1)))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) →
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (3 * n - 1)))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) →
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (3 * n - 1)))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) →
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (3 * n - 1)))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) →
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (3 * n - 1)))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) →
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (3 * n - 1)))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) →
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (3 * n - 1)))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Odd (a (n * (3 * n - 1))))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Odd (a (n * (3 * n - 1))))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Odd (a (n * (3 * n - 1))))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Odd (a (n * (3 * n - 1))))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Odd (a (n * (3 * n - 1))))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Odd (a (n * (3 * n - 1))))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Odd (a (n * (3 * n - 1))))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Odd (a (n * (2 * n - 1)))) ↔ (Odd (a (n * (3 * n - 1))))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Odd (a (n * (2 * n - 1)))) ↔ (Odd (a (n * (3 * n - 1))))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Odd (a (n * (2 * n - 1)))) ↔ (Odd (a (n * (3 * n - 1))))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Odd (a (n * (2 * n - 1)))) ↔ (Odd (a (n * (3 * n - 1))))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Odd (a (n * (2 * n - 1)))) ↔ (Odd (a (n * (3 * n - 1))))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Odd (a (n * (2 * n - 1)))) ↔ (Odd (a (n * (3 * n - 1))))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Odd (a (n * (2 * n - 1)))) ↔ (Odd (a (n * (3 * n - 1))))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 0), Odd (a (n * (2 * n - 1)))

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (n > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (n > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (n > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (n > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (n > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (n > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (n > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (n > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) ↔
    (∀ (n : ℕ) (hn : n > 0), Odd (a (n * (2 * n - 1)))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) ↔
    (∀ (n : ℕ) (hn : n > 0), Odd (a (n * (2 * n - 1)))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) ↔
    (∀ (n : ℕ) (hn : n > 0), Odd (a (n * (2 * n - 1)))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) ↔
    (∀ (n : ℕ) (hn : n > 0), Odd (a (n * (2 * n - 1)))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn₀ : 0 < n), Odd (a (n * (2 * n - 1)))

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) ↔
    (∀ (n : ℕ) (hn₀ : 0 < n), Odd (a (n * (2 * n - 1)))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) ↔
    (∀ (n : ℕ) (hn₀ : 0 < n), Odd (a (n * (2 * n - 1)))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) ↔
    (∀ (n : ℕ) (hn₀ : 0 < n), Odd (a (n * (2 * n - 1)))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) ↔
    (∀ (n : ℕ) (hn₀ : 0 < n), Odd (a (n * (2 * n - 1)))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : ¬(n ≤ 0)), Odd (a (n * (2 * n - 1)))

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 0)), Odd (a (n * (2 * n - 1)))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 0)), Odd (a (n * (2 * n - 1)))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 0)), Odd (a (n * (2 * n - 1)))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 0)), Odd (a (n * (2 * n - 1)))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), Odd (a (n * (2 * n - 1)))

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a (n * (2 * n - 1)))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a (n * (2 * n - 1)))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a (n * (2 * n - 1)))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a (n * (2 * n - 1)))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 0), Odd (a (n * (3 * n - 1)))

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), Odd (a (n * (3 * n - 1)))) →
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), Odd (a (n * (3 * n - 1)))) →
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), Odd (a (n * (3 * n - 1)))) →
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), Odd (a (n * (3 * n - 1)))) →
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), Odd (a (n * (3 * n - 1)))) →
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), Odd (a (n * (3 * n - 1)))) →
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), Odd (a (n * (3 * n - 1)))) →
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) →
    (∀ (n : ℕ) (hn : n > 0), Odd (a (n * (3 * n - 1)))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) →
    (∀ (n : ℕ) (hn : n > 0), Odd (a (n * (3 * n - 1)))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) →
    (∀ (n : ℕ) (hn : n > 0), Odd (a (n * (3 * n - 1)))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) →
    (∀ (n : ℕ) (hn : n > 0), Odd (a (n * (3 * n - 1)))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) →
    (∀ (n : ℕ) (hn : n > 0), Odd (a (n * (3 * n - 1)))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) →
    (∀ (n : ℕ) (hn : n > 0), Odd (a (n * (3 * n - 1)))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) →
    (∀ (n : ℕ) (hn : n > 0), Odd (a (n * (3 * n - 1)))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Odd (a (n * (3 * n - 1))))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Odd (a (n * (3 * n - 1))))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Odd (a (n * (3 * n - 1))))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Odd (a (n * (3 * n - 1))))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Odd (a (n * (3 * n - 1))))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Odd (a (n * (3 * n - 1))))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Odd (a (n * (3 * n - 1))))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Odd (a (n * (2 * n - 1)))) ↔ (Odd (a (n * (3 * n - 1))))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Odd (a (n * (2 * n - 1)))) ↔ (Odd (a (n * (3 * n - 1))))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Odd (a (n * (2 * n - 1)))) ↔ (Odd (a (n * (3 * n - 1))))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Odd (a (n * (2 * n - 1)))) ↔ (Odd (a (n * (3 * n - 1))))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Odd (a (n * (2 * n - 1)))) ↔ (Odd (a (n * (3 * n - 1))))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Odd (a (n * (2 * n - 1)))) ↔ (Odd (a (n * (3 * n - 1))))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Odd (a (n * (2 * n - 1)))) ↔ (Odd (a (n * (3 * n - 1))))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), Odd (a (n * (3 * n - 1)))

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a (n * (3 * n - 1)))) →
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a (n * (3 * n - 1)))) →
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a (n * (3 * n - 1)))) →
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a (n * (3 * n - 1)))) →
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a (n * (3 * n - 1)))) →
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a (n * (3 * n - 1)))) →
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a (n * (3 * n - 1)))) →
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a (n * (3 * n - 1)))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a (n * (3 * n - 1)))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a (n * (3 * n - 1)))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a (n * (3 * n - 1)))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a (n * (3 * n - 1)))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a (n * (3 * n - 1)))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Odd (a (n * (2 * n - 1)))) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Odd (a (n * (3 * n - 1)))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Odd (a (n * (3 * n - 1))))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Odd (a (n * (3 * n - 1))))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Odd (a (n * (3 * n - 1))))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Odd (a (n * (3 * n - 1))))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Odd (a (n * (3 * n - 1))))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Odd (a (n * (3 * n - 1))))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Odd (a (n * (3 * n - 1))))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Odd (a (n * (2 * n - 1)))) ↔ (Odd (a (n * (3 * n - 1))))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Odd (a (n * (2 * n - 1)))) ↔ (Odd (a (n * (3 * n - 1))))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Odd (a (n * (2 * n - 1)))) ↔ (Odd (a (n * (3 * n - 1))))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Odd (a (n * (2 * n - 1)))) ↔ (Odd (a (n * (3 * n - 1))))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Odd (a (n * (2 * n - 1)))) ↔ (Odd (a (n * (3 * n - 1))))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Odd (a (n * (2 * n - 1)))) ↔ (Odd (a (n * (3 * n - 1))))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Odd (a (n * (2 * n - 1)))) ↔ (Odd (a (n * (3 * n - 1))))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 0 < n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 0 < n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 0 < n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 0 < n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 0 < n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
