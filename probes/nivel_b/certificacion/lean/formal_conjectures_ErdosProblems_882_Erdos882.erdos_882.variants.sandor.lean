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
  ∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ) (hm : 1 < m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : 1 < m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : 1 < m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : 1 < m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : 1 < m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : 1 < m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : 1 < m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : 1 < m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (m : ℕ)  :
    (1 ≤ m) ↔ (1 < m) := by
  omega

set_option maxHeartbeats 200000 in
example (m : ℕ)  :
    (1 ≤ m) ↔ (1 < m) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (m : ℕ)  :
    (1 ≤ m) ↔ (1 < m) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (m : ℕ)  :
    (1 ≤ m) ↔ (1 < m) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (m : ℕ)  :
    (1 ≤ m) ↔ (1 < m) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (m : ℕ)  :
    (1 ≤ m) ↔ (1 < m) := by
  simp_all

set_option maxHeartbeats 200000 in
example (m : ℕ)  :
    (1 ≤ m) ↔ (1 < m) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((1 ≤ m) ↔ (1 < m))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((1 ≤ m) ↔ (1 < m))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((1 ≤ m) ↔ (1 < m))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((1 ≤ m) ↔ (1 < m))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((1 ≤ m) ↔ (1 < m))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((1 ≤ m) ↔ (1 < m))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 ≤ m) ↔ (1 < m)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 ≤ m) ↔ (1 < m)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 ≤ m) ↔ (1 < m)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 ≤ m) ↔ (1 < m)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 ≤ m) ↔ (1 < m)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 ≤ m) ↔ (1 < m)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m))

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (1 ≤ m) ∧ (¬(IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m)))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (1 ≤ m) ∧ (¬(IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m)))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (1 ≤ m) ∧ (¬(IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m)))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (1 ≤ m) ∧ (¬(IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m)))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (1 ≤ m) ∧ (¬(IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m)))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (1 ≤ m) ∧ (¬(IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m)))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (1 ≤ m) ∧ (¬(IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m)))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) ↔ (IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m)))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) ↔ (IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m)))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) ↔ (IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m)))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) ↔ (IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m)))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) ↔ (IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m)))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) ↔ (IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m)))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) ↔ (IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m)))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ) (hm : m ≥ 1), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (m ≥ 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (m ≥ 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (m ≥ 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (m ≥ 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (m ≥ 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (m ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (m ≥ 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (m ≥ 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) ↔
    (∀ (m : ℕ) (hm : m ≥ 1), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) ↔
    (∀ (m : ℕ) (hm : m ≥ 1), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) ↔
    (∀ (m : ℕ) (hm : m ≥ 1), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) ↔
    (∀ (m : ℕ) (hm : m ≥ 1), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ) (hm₀ : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) ↔
    (∀ (m : ℕ) (hm₀ : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) ↔
    (∀ (m : ℕ) (hm₀ : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) ↔
    (∀ (m : ℕ) (hm₀ : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) ↔
    (∀ (m : ℕ) (hm₀ : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ) (hm : ¬(m < 1)), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (¬(m < 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (¬(m < 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (¬(m < 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (¬(m < 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (¬(m < 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (¬(m < 1)) := by
  omega

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (¬(m < 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (¬(m < 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) ↔
    (∀ (m : ℕ) (hm : ¬(m < 1)), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) ↔
    (∀ (m : ℕ) (hm : ¬(m < 1)), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) ↔
    (∀ (m : ℕ) (hm : ¬(m < 1)), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) ↔
    (∀ (m : ℕ) (hm : ¬(m < 1)), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ) (hm : 0 < m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (0 < m) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (0 < m) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (0 < m) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (0 < m) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (0 < m) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (0 < m) := by
  omega

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (0 < m) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (1 ≤ m) ↔ (0 < m) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) ↔
    (∀ (m : ℕ) (hm : 0 < m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) ↔
    (∀ (m : ℕ) (hm : 0 < m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) ↔
    (∀ (m : ℕ) (hm : 0 < m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) ↔
    (∀ (m : ℕ) (hm : 0 < m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ) (hm : m > 1), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : m > 1), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : m > 1), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : m > 1), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : m > 1), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : m > 1), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : m > 1), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : m > 1), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (m : ℕ)  :
    (1 ≤ m) ↔ (m > 1) := by
  omega

set_option maxHeartbeats 200000 in
example (m : ℕ)  :
    (1 ≤ m) ↔ (m > 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (m : ℕ)  :
    (1 ≤ m) ↔ (m > 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (m : ℕ)  :
    (1 ≤ m) ↔ (m > 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (m : ℕ)  :
    (1 ≤ m) ↔ (m > 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (m : ℕ)  :
    (1 ≤ m) ↔ (m > 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example (m : ℕ)  :
    (1 ≤ m) ↔ (m > 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((1 ≤ m) ↔ (m > 1))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((1 ≤ m) ↔ (m > 1))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((1 ≤ m) ↔ (m > 1))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((1 ≤ m) ↔ (m > 1))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((1 ≤ m) ↔ (m > 1))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((1 ≤ m) ↔ (m > 1))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 ≤ m) ↔ (m > 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 ≤ m) ↔ (m > 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 ≤ m) ↔ (m > 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 ≤ m) ↔ (m > 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 ≤ m) ↔ (m > 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 ≤ m) ↔ (m > 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ) (hm : m ≥ 1), IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m))

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : m ≥ 1), IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : m ≥ 1), IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : m ≥ 1), IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : m ≥ 1), IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : m ≥ 1), IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : m ≥ 1), IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : m ≥ 1), IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : m ≥ 1), IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : m ≥ 1), IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : m ≥ 1), IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : m ≥ 1), IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : m ≥ 1), IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : m ≥ 1), IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : m ≥ 1), IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (1 ≤ m) ∧ (¬(IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m)))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (1 ≤ m) ∧ (¬(IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m)))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (1 ≤ m) ∧ (¬(IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m)))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (1 ≤ m) ∧ (¬(IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m)))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (1 ≤ m) ∧ (¬(IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m)))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (1 ≤ m) ∧ (¬(IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m)))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (1 ≤ m) ∧ (¬(IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m)))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) ↔ (IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m)))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) ↔ (IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m)))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) ↔ (IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m)))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) ↔ (IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m)))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) ↔ (IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m)))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) ↔ (IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m)))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) ↔ (IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m)))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ) (hm : 0 < m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m))

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : 0 < m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : 0 < m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : 0 < m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : 0 < m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : 0 < m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : 0 < m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) →
    (∀ (m : ℕ) (hm : 0 < m), IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (1 ≤ m) ∧ (¬(IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m)))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (1 ≤ m) ∧ (¬(IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m)))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (1 ≤ m) ∧ (¬(IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m)))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (1 ≤ m) ∧ (¬(IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m)))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (1 ≤ m) ∧ (¬(IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m)))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (1 ≤ m) ∧ (¬(IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m)))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (1 ≤ m) ∧ (¬(IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m)))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) ↔ (IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m)))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) ↔ (IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m)))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) ↔ (IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m)))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) ↔ (IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m)))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) ↔ (IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m)))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) ↔ (IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m)))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((IsSubsetSumAntichain ((Finset.range m).image (fun i => 2 ^ i + m * 2 ^ m))) ↔ (IsSubsetSumAntichain ((Finset.range m).image (fun i => 3 ^ i + m * 2 ^ m)))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (m : ℕ) (hm : 1 ≤ m) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (m : ℕ) (hm : 1 ≤ m) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (m : ℕ) (hm : 1 ≤ m) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (m : ℕ) (hm : 1 ≤ m) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (m : ℕ) (hm : 1 ≤ m) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
