import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 882

*References:*
- [erdosproblems.com/882](https://www.erdosproblems.com/882)
- [Er98] Erdős, Paul, *Some of my new and almost new problems and results in combinatorial
  number theory*. Number theory (Eger, 1996) (1998), 169-180.
- [ELRSS99] Erdős, P., Lev, V., Rauzy, G., Sándor, C. and Sárközy, A., *Greedy algorithm,
  arithmetic progressions, subset sums and divisibility*. Discrete Math. (1999), 119-135.
- [Erdős Problem 1](https://www.erdosproblems.com/1) for the upper bound.
- [Alexeev] Boris Alexeev's sorry-free Lean 4 formalisation of the lower bound,
  [plby/lean-proofs](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos882.lean).
-/

section

open Finset

namespace Erdos882

/--
A finite set `A` of naturals is *subset-sum antichain* if no two distinct nonempty subsets of
`A` have subset sums dividing one another.
-/
def IsSubsetSumAntichain (A : Finset ℕ) : Prop :=
  ∀ S₁ ⊆ A, ∀ S₂ ⊆ A, S₁.Nonempty → S₂.Nonempty → S₁ ≠ S₂ →
    ¬ (∑ a ∈ S₁, a) ∣ (∑ a ∈ S₂, a)

/-- The largest size of a subset-sum antichain contained in `{1, ..., n}`. -/
noncomputable def maxAntichainCard (n : ℕ) : ℕ :=
  sSup {k | ∃ A ⊆ Finset.Icc 1 n, IsSubsetSumAntichain A ∧ A.card = k}

/--
The construction of [ELRSS99]: $A_m = \{2^m - 2^i : 0 \leq i < m\}$.
-/
def A (m : ℕ) : Finset ℕ := (Finset.range m).image (fun i => 2 ^ m - 2 ^ i)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 ≤ (maxAntichainCard n : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 ≤ (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 ≤ (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 ≤ (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 ≤ (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 ≤ (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 ≤ (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 ≤ (maxAntichainCard n : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 2 n - 1 ≤ (maxAntichainCard n : ℝ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 2 n - 1 ≤ (maxAntichainCard n : ℝ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 2 n - 1 ≤ (maxAntichainCard n : ℝ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 2 n - 1 ≤ (maxAntichainCard n : ℝ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 2 n - 1 ≤ (maxAntichainCard n : ℝ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 2 n - 1 ≤ (maxAntichainCard n : ℝ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), Real.logb 3 n - 1 < (maxAntichainCard n : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 3 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 3 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 3 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 3 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 3 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 3 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 3 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 3 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 3 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 3 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 3 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 3 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 3 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 3 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Real.logb 3 n - 1 < (maxAntichainCard n : ℝ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Real.logb 3 n - 1 < (maxAntichainCard n : ℝ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Real.logb 3 n - 1 < (maxAntichainCard n : ℝ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Real.logb 3 n - 1 < (maxAntichainCard n : ℝ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Real.logb 3 n - 1 < (maxAntichainCard n : ℝ))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Real.logb 3 n - 1 < (maxAntichainCard n : ℝ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Real.logb 3 n - 1 < (maxAntichainCard n : ℝ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 3 n - 1 < (maxAntichainCard n : ℝ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 3 n - 1 < (maxAntichainCard n : ℝ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 3 n - 1 < (maxAntichainCard n : ℝ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 3 n - 1 < (maxAntichainCard n : ℝ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 3 n - 1 < (maxAntichainCard n : ℝ))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 3 n - 1 < (maxAntichainCard n : ℝ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 3 n - 1 < (maxAntichainCard n : ℝ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 > (maxAntichainCard n : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 > (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 > (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 > (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 > (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 > (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 > (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 > (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 > (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 > (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 > (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 > (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 > (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 > (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 > (maxAntichainCard n : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Real.logb 2 n - 1 > (maxAntichainCard n : ℝ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Real.logb 2 n - 1 > (maxAntichainCard n : ℝ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Real.logb 2 n - 1 > (maxAntichainCard n : ℝ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Real.logb 2 n - 1 > (maxAntichainCard n : ℝ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Real.logb 2 n - 1 > (maxAntichainCard n : ℝ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Real.logb 2 n - 1 > (maxAntichainCard n : ℝ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 2 n - 1 > (maxAntichainCard n : ℝ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 2 n - 1 > (maxAntichainCard n : ℝ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 2 n - 1 > (maxAntichainCard n : ℝ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 2 n - 1 > (maxAntichainCard n : ℝ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 2 n - 1 > (maxAntichainCard n : ℝ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 2 n - 1 > (maxAntichainCard n : ℝ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 0), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)

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
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔
    (∀ (n : ℕ) (hn : n > 0), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔
    (∀ (n : ℕ) (hn : n > 0), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔
    (∀ (n : ℕ) (hn : n > 0), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔
    (∀ (n : ℕ) (hn : n > 0), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), (maxAntichainCard n : ℝ) > Real.logb 2 n - 1

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ ((maxAntichainCard n : ℝ) > Real.logb 2 n - 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ ((maxAntichainCard n : ℝ) > Real.logb 2 n - 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ ((maxAntichainCard n : ℝ) > Real.logb 2 n - 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ ((maxAntichainCard n : ℝ) > Real.logb 2 n - 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ ((maxAntichainCard n : ℝ) > Real.logb 2 n - 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ ((maxAntichainCard n : ℝ) > Real.logb 2 n - 1) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ ((maxAntichainCard n : ℝ) > Real.logb 2 n - 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ ((maxAntichainCard n : ℝ) > Real.logb 2 n - 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔
    (∀ (n : ℕ) (hn : 0 < n), (maxAntichainCard n : ℝ) > Real.logb 2 n - 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔
    (∀ (n : ℕ) (hn : 0 < n), (maxAntichainCard n : ℝ) > Real.logb 2 n - 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔
    (∀ (n : ℕ) (hn : 0 < n), (maxAntichainCard n : ℝ) > Real.logb 2 n - 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔
    (∀ (n : ℕ) (hn : 0 < n), (maxAntichainCard n : ℝ) > Real.logb 2 n - 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn₀ : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔
    (∀ (n : ℕ) (hn₀ : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔
    (∀ (n : ℕ) (hn₀ : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔
    (∀ (n : ℕ) (hn₀ : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔
    (∀ (n : ℕ) (hn₀ : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : ¬(n ≤ 0)), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)

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
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 0)), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 0)), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 0)), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 0)), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)

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
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 0), Real.logb 2 n - 1 ≤ (maxAntichainCard n : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), Real.logb 2 n - 1 ≤ (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), Real.logb 2 n - 1 ≤ (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), Real.logb 2 n - 1 ≤ (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), Real.logb 2 n - 1 ≤ (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), Real.logb 2 n - 1 ≤ (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), Real.logb 2 n - 1 ≤ (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), Real.logb 2 n - 1 ≤ (maxAntichainCard n : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 2 n - 1 ≤ (maxAntichainCard n : ℝ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 2 n - 1 ≤ (maxAntichainCard n : ℝ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 2 n - 1 ≤ (maxAntichainCard n : ℝ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 2 n - 1 ≤ (maxAntichainCard n : ℝ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 2 n - 1 ≤ (maxAntichainCard n : ℝ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 2 n - 1 ≤ (maxAntichainCard n : ℝ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 0), Real.logb 3 n - 1 < (maxAntichainCard n : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), Real.logb 3 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), Real.logb 3 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), Real.logb 3 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), Real.logb 3 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), Real.logb 3 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), Real.logb 3 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), Real.logb 3 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), Real.logb 3 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), Real.logb 3 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), Real.logb 3 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), Real.logb 3 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), Real.logb 3 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), Real.logb 3 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), Real.logb 3 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Real.logb 3 n - 1 < (maxAntichainCard n : ℝ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Real.logb 3 n - 1 < (maxAntichainCard n : ℝ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Real.logb 3 n - 1 < (maxAntichainCard n : ℝ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Real.logb 3 n - 1 < (maxAntichainCard n : ℝ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Real.logb 3 n - 1 < (maxAntichainCard n : ℝ))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Real.logb 3 n - 1 < (maxAntichainCard n : ℝ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Real.logb 3 n - 1 < (maxAntichainCard n : ℝ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 3 n - 1 < (maxAntichainCard n : ℝ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 3 n - 1 < (maxAntichainCard n : ℝ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 3 n - 1 < (maxAntichainCard n : ℝ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 3 n - 1 < (maxAntichainCard n : ℝ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 3 n - 1 < (maxAntichainCard n : ℝ))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 3 n - 1 < (maxAntichainCard n : ℝ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 3 n - 1 < (maxAntichainCard n : ℝ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 0), Real.logb 2 n - 1 > (maxAntichainCard n : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), Real.logb 2 n - 1 > (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), Real.logb 2 n - 1 > (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), Real.logb 2 n - 1 > (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), Real.logb 2 n - 1 > (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), Real.logb 2 n - 1 > (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), Real.logb 2 n - 1 > (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), Real.logb 2 n - 1 > (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), Real.logb 2 n - 1 > (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), Real.logb 2 n - 1 > (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), Real.logb 2 n - 1 > (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), Real.logb 2 n - 1 > (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), Real.logb 2 n - 1 > (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), Real.logb 2 n - 1 > (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : n > 0), Real.logb 2 n - 1 > (maxAntichainCard n : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Real.logb 2 n - 1 > (maxAntichainCard n : ℝ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Real.logb 2 n - 1 > (maxAntichainCard n : ℝ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Real.logb 2 n - 1 > (maxAntichainCard n : ℝ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Real.logb 2 n - 1 > (maxAntichainCard n : ℝ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Real.logb 2 n - 1 > (maxAntichainCard n : ℝ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Real.logb 2 n - 1 > (maxAntichainCard n : ℝ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 2 n - 1 > (maxAntichainCard n : ℝ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 2 n - 1 > (maxAntichainCard n : ℝ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 2 n - 1 > (maxAntichainCard n : ℝ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 2 n - 1 > (maxAntichainCard n : ℝ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 2 n - 1 > (maxAntichainCard n : ℝ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 2 n - 1 > (maxAntichainCard n : ℝ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), (maxAntichainCard n : ℝ) ≥ Real.logb 2 n - 1

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), (maxAntichainCard n : ℝ) ≥ Real.logb 2 n - 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), (maxAntichainCard n : ℝ) ≥ Real.logb 2 n - 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), (maxAntichainCard n : ℝ) ≥ Real.logb 2 n - 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), (maxAntichainCard n : ℝ) ≥ Real.logb 2 n - 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), (maxAntichainCard n : ℝ) ≥ Real.logb 2 n - 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), (maxAntichainCard n : ℝ) ≥ Real.logb 2 n - 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), (maxAntichainCard n : ℝ) ≥ Real.logb 2 n - 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ ((maxAntichainCard n : ℝ) ≥ Real.logb 2 n - 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ ((maxAntichainCard n : ℝ) ≥ Real.logb 2 n - 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ ((maxAntichainCard n : ℝ) ≥ Real.logb 2 n - 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ ((maxAntichainCard n : ℝ) ≥ Real.logb 2 n - 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ ((maxAntichainCard n : ℝ) ≥ Real.logb 2 n - 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ ((maxAntichainCard n : ℝ) ≥ Real.logb 2 n - 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), (maxAntichainCard n : ℝ) > Real.logb 3 n - 1

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), (maxAntichainCard n : ℝ) > Real.logb 3 n - 1) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), (maxAntichainCard n : ℝ) > Real.logb 3 n - 1) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), (maxAntichainCard n : ℝ) > Real.logb 3 n - 1) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), (maxAntichainCard n : ℝ) > Real.logb 3 n - 1) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), (maxAntichainCard n : ℝ) > Real.logb 3 n - 1) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), (maxAntichainCard n : ℝ) > Real.logb 3 n - 1) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), (maxAntichainCard n : ℝ) > Real.logb 3 n - 1) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), (maxAntichainCard n : ℝ) > Real.logb 3 n - 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), (maxAntichainCard n : ℝ) > Real.logb 3 n - 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), (maxAntichainCard n : ℝ) > Real.logb 3 n - 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), (maxAntichainCard n : ℝ) > Real.logb 3 n - 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), (maxAntichainCard n : ℝ) > Real.logb 3 n - 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), (maxAntichainCard n : ℝ) > Real.logb 3 n - 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), (maxAntichainCard n : ℝ) > Real.logb 3 n - 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((maxAntichainCard n : ℝ) > Real.logb 3 n - 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((maxAntichainCard n : ℝ) > Real.logb 3 n - 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((maxAntichainCard n : ℝ) > Real.logb 3 n - 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((maxAntichainCard n : ℝ) > Real.logb 3 n - 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((maxAntichainCard n : ℝ) > Real.logb 3 n - 1)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((maxAntichainCard n : ℝ) > Real.logb 3 n - 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((maxAntichainCard n : ℝ) > Real.logb 3 n - 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ ((maxAntichainCard n : ℝ) > Real.logb 3 n - 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ ((maxAntichainCard n : ℝ) > Real.logb 3 n - 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ ((maxAntichainCard n : ℝ) > Real.logb 3 n - 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ ((maxAntichainCard n : ℝ) > Real.logb 3 n - 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ ((maxAntichainCard n : ℝ) > Real.logb 3 n - 1)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ ((maxAntichainCard n : ℝ) > Real.logb 3 n - 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ ((maxAntichainCard n : ℝ) > Real.logb 3 n - 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), (maxAntichainCard n : ℝ) < Real.logb 2 n - 1

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), (maxAntichainCard n : ℝ) < Real.logb 2 n - 1) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), (maxAntichainCard n : ℝ) < Real.logb 2 n - 1) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), (maxAntichainCard n : ℝ) < Real.logb 2 n - 1) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), (maxAntichainCard n : ℝ) < Real.logb 2 n - 1) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), (maxAntichainCard n : ℝ) < Real.logb 2 n - 1) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), (maxAntichainCard n : ℝ) < Real.logb 2 n - 1) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), (maxAntichainCard n : ℝ) < Real.logb 2 n - 1) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), (maxAntichainCard n : ℝ) < Real.logb 2 n - 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), (maxAntichainCard n : ℝ) < Real.logb 2 n - 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), (maxAntichainCard n : ℝ) < Real.logb 2 n - 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), (maxAntichainCard n : ℝ) < Real.logb 2 n - 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), (maxAntichainCard n : ℝ) < Real.logb 2 n - 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), (maxAntichainCard n : ℝ) < Real.logb 2 n - 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), (maxAntichainCard n : ℝ) < Real.logb 2 n - 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((maxAntichainCard n : ℝ) < Real.logb 2 n - 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((maxAntichainCard n : ℝ) < Real.logb 2 n - 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((maxAntichainCard n : ℝ) < Real.logb 2 n - 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((maxAntichainCard n : ℝ) < Real.logb 2 n - 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((maxAntichainCard n : ℝ) < Real.logb 2 n - 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((maxAntichainCard n : ℝ) < Real.logb 2 n - 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ ((maxAntichainCard n : ℝ) < Real.logb 2 n - 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ ((maxAntichainCard n : ℝ) < Real.logb 2 n - 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ ((maxAntichainCard n : ℝ) < Real.logb 2 n - 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ ((maxAntichainCard n : ℝ) < Real.logb 2 n - 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ ((maxAntichainCard n : ℝ) < Real.logb 2 n - 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ ((maxAntichainCard n : ℝ) < Real.logb 2 n - 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), Real.logb 2 n - 1 ≤ (maxAntichainCard n : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Real.logb 2 n - 1 ≤ (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Real.logb 2 n - 1 ≤ (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Real.logb 2 n - 1 ≤ (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Real.logb 2 n - 1 ≤ (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Real.logb 2 n - 1 ≤ (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Real.logb 2 n - 1 ≤ (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Real.logb 2 n - 1 ≤ (maxAntichainCard n : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 2 n - 1 ≤ (maxAntichainCard n : ℝ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 2 n - 1 ≤ (maxAntichainCard n : ℝ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 2 n - 1 ≤ (maxAntichainCard n : ℝ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 2 n - 1 ≤ (maxAntichainCard n : ℝ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 2 n - 1 ≤ (maxAntichainCard n : ℝ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 2 n - 1 ≤ (maxAntichainCard n : ℝ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 1 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 1 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 1 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 1 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 1 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 1 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 1 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (0 < n) ↔ (1 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (0 < n) ↔ (1 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (0 < n) ↔ (1 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((0 < n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((0 < n) ↔ (1 < n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((0 < n) ↔ (1 < n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((0 < n) ↔ (1 < n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((0 < n) ↔ (1 < n))) :=
  ⟨(10 : ℕ), by norm_num⟩

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
  ∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), Real.logb 3 n - 1 < (maxAntichainCard n : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Real.logb 3 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Real.logb 3 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Real.logb 3 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Real.logb 3 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Real.logb 3 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Real.logb 3 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Real.logb 3 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Real.logb 3 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Real.logb 3 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Real.logb 3 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Real.logb 3 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Real.logb 3 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Real.logb 3 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Real.logb 3 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Real.logb 3 n - 1 < (maxAntichainCard n : ℝ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Real.logb 3 n - 1 < (maxAntichainCard n : ℝ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Real.logb 3 n - 1 < (maxAntichainCard n : ℝ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Real.logb 3 n - 1 < (maxAntichainCard n : ℝ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Real.logb 3 n - 1 < (maxAntichainCard n : ℝ))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Real.logb 3 n - 1 < (maxAntichainCard n : ℝ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Real.logb 3 n - 1 < (maxAntichainCard n : ℝ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 3 n - 1 < (maxAntichainCard n : ℝ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 3 n - 1 < (maxAntichainCard n : ℝ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 3 n - 1 < (maxAntichainCard n : ℝ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 3 n - 1 < (maxAntichainCard n : ℝ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 3 n - 1 < (maxAntichainCard n : ℝ))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 3 n - 1 < (maxAntichainCard n : ℝ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 3 n - 1 < (maxAntichainCard n : ℝ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), Real.logb 2 n - 1 > (maxAntichainCard n : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Real.logb 2 n - 1 > (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Real.logb 2 n - 1 > (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Real.logb 2 n - 1 > (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Real.logb 2 n - 1 > (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Real.logb 2 n - 1 > (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Real.logb 2 n - 1 > (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), Real.logb 2 n - 1 > (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Real.logb 2 n - 1 > (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Real.logb 2 n - 1 > (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Real.logb 2 n - 1 > (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Real.logb 2 n - 1 > (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Real.logb 2 n - 1 > (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Real.logb 2 n - 1 > (maxAntichainCard n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), Real.logb 2 n - 1 > (maxAntichainCard n : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Real.logb 2 n - 1 > (maxAntichainCard n : ℝ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Real.logb 2 n - 1 > (maxAntichainCard n : ℝ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Real.logb 2 n - 1 > (maxAntichainCard n : ℝ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Real.logb 2 n - 1 > (maxAntichainCard n : ℝ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Real.logb 2 n - 1 > (maxAntichainCard n : ℝ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(Real.logb 2 n - 1 > (maxAntichainCard n : ℝ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 2 n - 1 > (maxAntichainCard n : ℝ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 2 n - 1 > (maxAntichainCard n : ℝ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 2 n - 1 > (maxAntichainCard n : ℝ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 2 n - 1 > (maxAntichainCard n : ℝ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 2 n - 1 > (maxAntichainCard n : ℝ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((Real.logb 2 n - 1 < (maxAntichainCard n : ℝ)) ↔ (Real.logb 2 n - 1 > (maxAntichainCard n : ℝ))) :=
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
