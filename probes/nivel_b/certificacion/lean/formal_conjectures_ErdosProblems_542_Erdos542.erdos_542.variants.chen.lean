import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 542

*References:*
- [erdosproblems.com/542](https://www.erdosproblems.com/542)
- [Er73] Erdős, P., _Problems and results on combinatorial number theory_. A survey of
  combinatorial theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins, Colo., 1971)
  (1973), 117-138.
- [Er80] Erdős, Paul, _A survey of problems in combinatorial number theory_. Ann. Discrete Math.
  (1980), 89-115.
- [Er98] Erdős, Paul, _Some of my new and almost new problems and results in combinatorial number
  theory_. Number theory (Eger, 1996) (1998), 169-180.
- [ScSz59] Schinzel, A. and Szekeres, G., _Sur un problème de M. Paul Erdős_. Acta Sci. Math.
  (Szeged) (1959), 221-229.
- [Ch96] Chen, Yong-Gao, _On a problem of P. Erdős_. Acta Sci. Math. (Szeged) (1996), 101--114.
-/

section

open Filter Real

namespace Erdos542

/-- A set `A ⊆ {1, …, n}` such that `lcm(a, b) > n` for all distinct `a, b ∈ A`. -/
def IsLcmFree (n : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 n ∧ (A : Set ℕ).Pairwise fun a b ↦ n < Nat.lcm a b

/-- The integers `1 ≤ m ≤ n` which are not divisible by any element of `A`. -/
def uncovered (n : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun m ↦ ∀ a ∈ A, ¬ a ∣ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) (hA : IsLcmFree n A) :
    (172509 < n) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) (hA : IsLcmFree n A) :
    (172509 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) (hA : IsLcmFree n A) :
    (172509 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) (hA : IsLcmFree n A) :
    (172509 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) (hA : IsLcmFree n A) :
    (172509 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) (hA : IsLcmFree n A) :
    (172509 < n) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) (hA : IsLcmFree n A) :
    (172509 < n) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (True)) :=
  ⟨(172509 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (True)) :=
  ⟨(172508 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (True)) :=
  ⟨(172510 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 172509 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) (hA : IsLcmFree n A) :
    (172509 < n) ↔ (172509 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) (hA : IsLcmFree n A) :
    (172509 < n) ↔ (172509 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) (hA : IsLcmFree n A) :
    (172509 < n) ↔ (172509 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) (hA : IsLcmFree n A) :
    (172509 < n) ↔ (172509 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) (hA : IsLcmFree n A) :
    (172509 < n) ↔ (172509 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) (hA : IsLcmFree n A) :
    (172509 < n) ↔ (172509 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) (hA : IsLcmFree n A) :
    (172509 < n) ↔ (172509 ≤ n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (172509 ≤ n)) :=
  ⟨(172509 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (172509 ≤ n)) :=
  ⟨(172508 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (172509 ≤ n)) :=
  ⟨(172510 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (172509 ≤ n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (172509 ≤ n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (172509 ≤ n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (172509 ≤ n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (172509 ≤ n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (172509 ≤ n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a ≤ 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a ≤ 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a ≤ 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a ≤ 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a ≤ 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a ≤ 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a ≤ 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a ≤ 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 172510 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172510 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172510 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172510 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172510 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172510 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172510 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172510 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) (hA : IsLcmFree n A) :
    (172509 < n) ↔ (172510 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) (hA : IsLcmFree n A) :
    (172509 < n) ↔ (172510 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) (hA : IsLcmFree n A) :
    (172509 < n) ↔ (172510 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) (hA : IsLcmFree n A) :
    (172509 < n) ↔ (172510 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) (hA : IsLcmFree n A) :
    (172509 < n) ↔ (172510 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) (hA : IsLcmFree n A) :
    (172509 < n) ↔ (172510 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) (hA : IsLcmFree n A) :
    (172509 < n) ↔ (172510 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (172510 < n)) :=
  ⟨(172509 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (172510 < n)) :=
  ⟨(172508 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (172510 < n)) :=
  ⟨(172510 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (172510 < n)) :=
  ⟨(172511 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (172510 < n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (172510 < n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (172510 < n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (172510 < n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (172510 < n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (172510 < n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a > 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a > 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a > 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a > 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a > 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a > 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a > 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a > 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a > 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a > 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a > 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a > 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a > 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a > 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a > 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 172509) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) :
    (172509 < n) ↔ (n > 172509) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) :
    (172509 < n) ↔ (n > 172509) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) :
    (172509 < n) ↔ (n > 172509) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) :
    (172509 < n) ↔ (n > 172509) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) :
    (172509 < n) ↔ (n > 172509) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) :
    (172509 < n) ↔ (n > 172509) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) :
    (172509 < n) ↔ (n > 172509) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) :
    (172509 < n) ↔ (n > 172509) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) ↔
    (∀ (n : ℕ) (hn : n > 172509) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) ↔
    (∀ (n : ℕ) (hn : n > 172509) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) ↔
    (∀ (n : ℕ) (hn : n > 172509) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) ↔
    (∀ (n : ℕ) (hn : n > 172509) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn₀ : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) ↔
    (∀ (n : ℕ) (hn₀ : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) ↔
    (∀ (n : ℕ) (hn₀ : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) ↔
    (∀ (n : ℕ) (hn₀ : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) ↔
    (∀ (n : ℕ) (hn₀ : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : ¬(n ≤ 172509)) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) :
    (172509 < n) ↔ (¬(n ≤ 172509)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) :
    (172509 < n) ↔ (¬(n ≤ 172509)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) :
    (172509 < n) ↔ (¬(n ≤ 172509)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) :
    (172509 < n) ↔ (¬(n ≤ 172509)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) :
    (172509 < n) ↔ (¬(n ≤ 172509)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) :
    (172509 < n) ↔ (¬(n ≤ 172509)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) :
    (172509 < n) ↔ (¬(n ≤ 172509)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) :
    (172509 < n) ↔ (¬(n ≤ 172509)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 172509)) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 172509)) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 172509)) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 172509)) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 172510 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) :
    (172509 < n) ↔ (172510 ≤ n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) :
    (172509 < n) ↔ (172510 ≤ n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) :
    (172509 < n) ↔ (172510 ≤ n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) :
    (172509 < n) ↔ (172510 ≤ n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) :
    (172509 < n) ↔ (172510 ≤ n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) :
    (172509 < n) ↔ (172510 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) :
    (172509 < n) ↔ (172510 ≤ n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) :
    (172509 < n) ↔ (172510 ≤ n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) ↔
    (∀ (n : ℕ) (hn : 172510 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) ↔
    (∀ (n : ℕ) (hn : 172510 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) ↔
    (∀ (n : ℕ) (hn : 172510 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) ↔
    (∀ (n : ℕ) (hn : 172510 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 172509) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 172509) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 172509) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 172509) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 172509) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 172509) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 172509) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 172509) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) (hA : IsLcmFree n A) :
    (172509 < n) ↔ (n ≥ 172509) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) (hA : IsLcmFree n A) :
    (172509 < n) ↔ (n ≥ 172509) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) (hA : IsLcmFree n A) :
    (172509 < n) ↔ (n ≥ 172509) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) (hA : IsLcmFree n A) :
    (172509 < n) ↔ (n ≥ 172509) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) (hA : IsLcmFree n A) :
    (172509 < n) ↔ (n ≥ 172509) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) (hA : IsLcmFree n A) :
    (172509 < n) ↔ (n ≥ 172509) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) (hA : IsLcmFree n A) :
    (172509 < n) ↔ (n ≥ 172509) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (n ≥ 172509)) :=
  ⟨(172509 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (n ≥ 172509)) :=
  ⟨(172508 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (n ≥ 172509)) :=
  ⟨(172510 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (n ≥ 172509)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (n ≥ 172509)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (n ≥ 172509)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (n ≥ 172509)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (n ≥ 172509)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (n ≥ 172509)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 172509) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a ≤ 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : n > 172509) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a ≤ 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : n > 172509) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a ≤ 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : n > 172509) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a ≤ 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : n > 172509) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a ≤ 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : n > 172509) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a ≤ 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : n > 172509) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a ≤ 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : n > 172509) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a ≤ 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 172510) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : n > 172510) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : n > 172510) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : n > 172510) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : n > 172510) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : n > 172510) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : n > 172510) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : n > 172510) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) (hA : IsLcmFree n A) :
    (172509 < n) ↔ (n > 172510) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) (hA : IsLcmFree n A) :
    (172509 < n) ↔ (n > 172510) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) (hA : IsLcmFree n A) :
    (172509 < n) ↔ (n > 172510) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) (hA : IsLcmFree n A) :
    (172509 < n) ↔ (n > 172510) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) (hA : IsLcmFree n A) :
    (172509 < n) ↔ (n > 172510) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) (hA : IsLcmFree n A) :
    (172509 < n) ↔ (n > 172510) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) (hA : IsLcmFree n A) :
    (172509 < n) ↔ (n > 172510) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (n > 172510)) :=
  ⟨(172509 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (n > 172510)) :=
  ⟨(172508 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (n > 172510)) :=
  ⟨(172510 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (n > 172510)) :=
  ⟨(172511 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (n > 172510)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (n > 172510)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (n > 172510)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (n > 172510)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (n > 172510)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((172509 < n) ↔ (n > 172510)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 172509) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a > 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 172509) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a > 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 172509) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a > 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 172509) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a > 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 172509) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a > 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 172509) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a > 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 172509) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a > 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 172509) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a > 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : n > 172509) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a > 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : n > 172509) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a > 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : n > 172509) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a > 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : n > 172509) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a > 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : n > 172509) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a > 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : n > 172509) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a > 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : n > 172509) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a > 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 172510 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a ≤ 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172510 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a ≤ 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172510 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a ≤ 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172510 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a ≤ 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172510 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a ≤ 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172510 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a ≤ 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172510 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a ≤ 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172510 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a ≤ 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 172510 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 4 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172510 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 4 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172510 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 4 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172510 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 4 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172510 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 4 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172510 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 4 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172510 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 4 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172510 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 4 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172510 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 4 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172510 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 4 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172510 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 4 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172510 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 4 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172510 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 4 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172510 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 4 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172510 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 4 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 172510 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a > 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172510 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a > 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172510 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a > 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172510 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a > 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172510 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a > 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172510 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a > 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172510 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a > 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172510 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a > 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172510 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a > 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172510 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a > 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172510 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a > 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172510 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a > 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172510 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a > 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172510 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a > 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) →
    (∀ (n : ℕ) (hn : 172510 ≤ n) (A : Finset ℕ) (hA : IsLcmFree n A), ∑ a ∈ A, (1 : ℝ) / a > 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) (hn : 172509 < n) (hA : IsLcmFree n A) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) (hn : 172509 < n) (hA : IsLcmFree n A) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) (hn : 172509 < n) (hA : IsLcmFree n A) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) (hn : 172509 < n) (hA : IsLcmFree n A) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (A : Finset ℕ) (hn : 172509 < n) (hA : IsLcmFree n A) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
