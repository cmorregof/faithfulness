import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 17
*Reference:* [erdosproblems.com/17](https://www.erdosproblems.com/17)
-/

section

open Filter Asymptotics Real

namespace Erdos17

/-- A prime $p$ is a cluster prime if every even natural number
$n \le p - 3$ can be written as a difference of two primes
$q_1 - q_2$ with $q_1, q_2 \le p$. -/
def IsClusterPrime (p : ℕ) : Prop :=
  p.Prime ∧
    ∀ {n : ℕ}, Even n → n ≤ (p - 3 : ℤ) →
      ∃ q₁ q₂ : ℕ, q₁.Prime ∧ q₂.Prime ∧
        q₁ ≤ p ∧ q₂ ≤ p ∧ n = (q₁ - q₂ : ℤ)

/-- The counting function of cluster primes $\le n$. -/
noncomputable def clusterPrimeCount (n : ℕ) : ℕ :=
  Nat.card {p : ℕ | p ≤ n ∧ IsClusterPrime p}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℝ} (hA : 0 < A), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℝ} (hA : 0 ≤ A), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℝ} (hA : 0 ≤ A), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) →
    (∀ {A : ℝ} (hA : 0 < A), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℝ} (hA : 0 ≤ A), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) →
    (∀ {A : ℝ} (hA : 0 < A), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℝ} (hA : 0 ≤ A), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) →
    (∀ {A : ℝ} (hA : 0 < A), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℝ} (hA : 0 ≤ A), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) →
    (∀ {A : ℝ} (hA : 0 < A), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℝ} (hA : 0 ≤ A), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) →
    (∀ {A : ℝ} (hA : 0 < A), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℝ} (hA : 0 ≤ A), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) →
    (∀ {A : ℝ} (hA : 0 < A), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℝ} (hA : 0 ≤ A), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) →
    (∀ {A : ℝ} (hA : 0 < A), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {A : ℝ}  :
    (0 < A) ↔ (0 ≤ A) := by
  omega

set_option maxHeartbeats 200000 in
example {A : ℝ}  :
    (0 < A) ↔ (0 ≤ A) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {A : ℝ}  :
    (0 < A) ↔ (0 ≤ A) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {A : ℝ}  :
    (0 < A) ↔ (0 ≤ A) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {A : ℝ}  :
    (0 < A) ↔ (0 ≤ A) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {A : ℝ}  :
    (0 < A) ↔ (0 ≤ A) := by
  simp_all

set_option maxHeartbeats 200000 in
example {A : ℝ}  :
    (0 < A) ↔ (0 ≤ A) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ), (¬((0 < A) ↔ (0 ≤ A))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ), (¬((0 < A) ↔ (0 ≤ A))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ), (¬((0 < A) ↔ (0 ≤ A))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ), (¬((0 < A) ↔ (0 ≤ A))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ), (¬((0 < A) ↔ (0 ≤ A))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ), (¬((0 < A) ↔ (0 ≤ A))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ), ¬((0 < A) ↔ (0 ≤ A)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ), ¬((0 < A) ↔ (0 ≤ A)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ), ¬((0 < A) ↔ (0 ≤ A)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ), ¬((0 < A) ↔ (0 ≤ A)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ), ¬((0 < A) ↔ (0 ≤ A)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ), ¬((0 < A) ↔ (0 ≤ A)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℝ} (hA : 0 < A), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℝ} (hA : A > 0), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A

set_option maxHeartbeats 200000 in
example {A : ℝ} :
    (0 < A) ↔ (A > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {A : ℝ} :
    (0 < A) ↔ (A > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {A : ℝ} :
    (0 < A) ↔ (A > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {A : ℝ} :
    (0 < A) ↔ (A > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {A : ℝ} :
    (0 < A) ↔ (A > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {A : ℝ} :
    (0 < A) ↔ (A > 0) := by
  omega

set_option maxHeartbeats 200000 in
example {A : ℝ} :
    (0 < A) ↔ (A > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {A : ℝ} :
    (0 < A) ↔ (A > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℝ} (hA : 0 < A), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) ↔
    (∀ {A : ℝ} (hA : A > 0), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℝ} (hA : 0 < A), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) ↔
    (∀ {A : ℝ} (hA : A > 0), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℝ} (hA : 0 < A), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) ↔
    (∀ {A : ℝ} (hA : A > 0), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℝ} (hA : 0 < A), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) ↔
    (∀ {A : ℝ} (hA : A > 0), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℝ} (hA : 0 < A), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℝ} (hA₀ : 0 < A), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℝ} (hA : 0 < A), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) ↔
    (∀ {A : ℝ} (hA₀ : 0 < A), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℝ} (hA : 0 < A), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) ↔
    (∀ {A : ℝ} (hA₀ : 0 < A), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℝ} (hA : 0 < A), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) ↔
    (∀ {A : ℝ} (hA₀ : 0 < A), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℝ} (hA : 0 < A), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) ↔
    (∀ {A : ℝ} (hA₀ : 0 < A), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℝ} (hA : 0 < A), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℝ} (hA : ¬(A ≤ 0)), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A

set_option maxHeartbeats 200000 in
example {A : ℝ} :
    (0 < A) ↔ (¬(A ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {A : ℝ} :
    (0 < A) ↔ (¬(A ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {A : ℝ} :
    (0 < A) ↔ (¬(A ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {A : ℝ} :
    (0 < A) ↔ (¬(A ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {A : ℝ} :
    (0 < A) ↔ (¬(A ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {A : ℝ} :
    (0 < A) ↔ (¬(A ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example {A : ℝ} :
    (0 < A) ↔ (¬(A ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {A : ℝ} :
    (0 < A) ↔ (¬(A ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℝ} (hA : 0 < A), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) ↔
    (∀ {A : ℝ} (hA : ¬(A ≤ 0)), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℝ} (hA : 0 < A), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) ↔
    (∀ {A : ℝ} (hA : ¬(A ≤ 0)), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℝ} (hA : 0 < A), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) ↔
    (∀ {A : ℝ} (hA : ¬(A ≤ 0)), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℝ} (hA : 0 < A), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) ↔
    (∀ {A : ℝ} (hA : ¬(A ≤ 0)), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℝ} (hA : 0 < A), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A : ℝ} (hA : A ≥ 0), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℝ} (hA : A ≥ 0), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) →
    (∀ {A : ℝ} (hA : 0 < A), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℝ} (hA : A ≥ 0), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) →
    (∀ {A : ℝ} (hA : 0 < A), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℝ} (hA : A ≥ 0), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) →
    (∀ {A : ℝ} (hA : 0 < A), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℝ} (hA : A ≥ 0), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) →
    (∀ {A : ℝ} (hA : 0 < A), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℝ} (hA : A ≥ 0), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) →
    (∀ {A : ℝ} (hA : 0 < A), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℝ} (hA : A ≥ 0), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) →
    (∀ {A : ℝ} (hA : 0 < A), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {A : ℝ} (hA : A ≥ 0), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) →
    (∀ {A : ℝ} (hA : 0 < A), (fun x ↦ (clusterPrimeCount x : ℝ)) =O[atTop] fun x ↦ x / (log x) ^ A) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {A : ℝ}  :
    (0 < A) ↔ (A ≥ 0) := by
  omega

set_option maxHeartbeats 200000 in
example {A : ℝ}  :
    (0 < A) ↔ (A ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {A : ℝ}  :
    (0 < A) ↔ (A ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {A : ℝ}  :
    (0 < A) ↔ (A ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {A : ℝ}  :
    (0 < A) ↔ (A ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {A : ℝ}  :
    (0 < A) ↔ (A ≥ 0) := by
  simp_all

set_option maxHeartbeats 200000 in
example {A : ℝ}  :
    (0 < A) ↔ (A ≥ 0) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ), (¬((0 < A) ↔ (A ≥ 0))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ), (¬((0 < A) ↔ (A ≥ 0))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ), (¬((0 < A) ↔ (A ≥ 0))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ), (¬((0 < A) ↔ (A ≥ 0))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ), (¬((0 < A) ↔ (A ≥ 0))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ), (¬((0 < A) ↔ (A ≥ 0))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ), ¬((0 < A) ↔ (A ≥ 0)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ), ¬((0 < A) ↔ (A ≥ 0)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ), ¬((0 < A) ↔ (A ≥ 0)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ), ¬((0 < A) ↔ (A ≥ 0)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ), ¬((0 < A) ↔ (A ≥ 0)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ), ¬((0 < A) ↔ (A ≥ 0)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {A : ℝ} (hA : 0 < A) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {A : ℝ} (hA : 0 < A) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {A : ℝ} (hA : 0 < A) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {A : ℝ} (hA : 0 < A) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {A : ℝ} (hA : 0 < A) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
