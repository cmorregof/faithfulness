import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 745: Second-largest component of a random graph

*Reference:* [erdosproblems.com/745](https://www.erdosproblems.com/745)

At the stated parameter $p=1/n$, the second-largest component has order
$n^{2/3}$ in probability. The logarithmic bound applies to fixed
$p=\lambda/n$ with $\lambda>1$.

[Al97] Aldous, D., Brownian excursions, critical random graphs and the multiplicative
coalescent. Ann. Probab. 25 (1997), 812–854.

[KSS80] Komlós, J., Sulyok, M. and Szemerédi, E., Second largest component in a random
graph. Studia Sci. Math. Hungar. 15 (1980), 391–395.
-/

section

open MeasureTheory
open scoped Topology unitInterval

namespace Erdos745

/-- The edge probability $1/n$, with zero at the empty index. -/
noncomputable def criticalEdgeProbability (n : ℕ) : unitInterval :=
  if hn : n = 0 then 0 else
    ⟨(1 : ℝ) / n, unitInterval.div_mem (by positivity) (Nat.cast_nonneg n)
      (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn))⟩

/-- The independent-edge random graph $G(n,1/n)$. -/
noncomputable def criticalRandomGraph (n : ℕ) : Measure (SimpleGraph (Fin n)) :=
  SimpleGraph.binomialRandom (Fin n) (criticalEdgeProbability n)

/-- The multiset of component sizes, retaining repetitions. -/
noncomputable def componentOrders {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Multiset ℕ := by
  classical
  exact (Finset.univ : Finset G.ConnectedComponent).val.map fun C ↦ C.supp.ncard

/-- Component sizes listed in decreasing order. -/
noncomputable def rankedComponentOrders {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : List ℕ :=
  (componentOrders G).sort (· ≥ ·)

/-- The second-largest component size, or zero if fewer than two components exist. -/
noncomputable def secondLargestComponentOrder {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) : ℕ :=
  (rankedComponentOrders G).getD 1 0

/-- The probability of an event in $G(n,1/n)$. -/
noncomputable def criticalProbability (n : ℕ)
    (P : SimpleGraph (Fin n) → Prop) : ℝ :=
  (criticalRandomGraph n).real {G | P G}

/-- The edge probability $\lambda/n$, clipped to $[0,1]$ at small indices. -/
noncomputable def edgeProbability (lam : ℝ) (n : ℕ) : unitInterval :=
  ⟨max 0 (min 1 (lam / n)), le_max_left _ _,
    max_le zero_le_one (min_le_left _ _)⟩

/-- The independent-edge random graph with clipped edge probability $\lambda/n$. -/
noncomputable def randomGraph (lam : ℝ) (n : ℕ) : Measure (SimpleGraph (Fin n)) :=
  SimpleGraph.binomialRandom (Fin n) (edgeProbability lam n)

/-- The probability of an event in the model with parameter $\lambda$. -/
noncomputable def probability (lam : ℝ) (n : ℕ)
    (P : SimpleGraph (Fin n) → Prop) : ℝ :=
  (randomGraph lam n).real {G | P G}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (lam : ℝ) (hlam : 1 < lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (lam : ℝ) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) →
    (∀ (lam : ℝ) (hlam : 1 < lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) →
    (∀ (lam : ℝ) (hlam : 1 < lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) →
    (∀ (lam : ℝ) (hlam : 1 < lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) →
    (∀ (lam : ℝ) (hlam : 1 < lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) →
    (∀ (lam : ℝ) (hlam : 1 < lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) →
    (∀ (lam : ℝ) (hlam : 1 < lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) →
    (∀ (lam : ℝ) (hlam : 1 < lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (lam : ℝ) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A) :
    (1 < lam) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (lam : ℝ) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A) :
    (1 < lam) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (lam : ℝ) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A) :
    (1 < lam) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (lam : ℝ) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A) :
    (1 < lam) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (lam : ℝ) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A) :
    (1 < lam) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (lam : ℝ) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A) :
    (1 < lam) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (lam : ℝ) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A) :
    (1 < lam) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (True))) :=
  ⟨(1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (True))) :=
  ⟨(2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (True))) :=
  ⟨(1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (True))) :=
  ⟨(0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (True))) :=
  ⟨(2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (True))) :=
  ⟨(-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (True))) :=
  ⟨(1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (True))) :=
  ⟨(2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (True))) :=
  ⟨(1/2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (True))) :=
  ⟨(1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (True))) :=
  ⟨(0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (True))) :=
  ⟨(2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (True))) :=
  ⟨(-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (True))) :=
  ⟨(1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (True))) :=
  ⟨(3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (True))) :=
  ⟨(0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (True))) :=
  ⟨(2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (True))) :=
  ⟨(1/2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (True))) :=
  ⟨(3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (True))) :=
  ⟨(2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (True))) :=
  ⟨(-1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (True))) :=
  ⟨(1/2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (True))) :=
  ⟨(3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (True))) :=
  ⟨(-1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (True))) :=
  ⟨(1/2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), ¬((1 < lam) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), ¬((1 < lam) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), ¬((1 < lam) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), ¬((1 < lam) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), ¬((1 < lam) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), ¬((1 < lam) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (lam : ℝ) (hlam : 1 < lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (lam : ℝ) (hlam : 1 ≤ lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 1 ≤ lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) →
    (∀ (lam : ℝ) (hlam : 1 < lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 1 ≤ lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) →
    (∀ (lam : ℝ) (hlam : 1 < lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 1 ≤ lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) →
    (∀ (lam : ℝ) (hlam : 1 < lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 1 ≤ lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) →
    (∀ (lam : ℝ) (hlam : 1 < lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 1 ≤ lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) →
    (∀ (lam : ℝ) (hlam : 1 < lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 1 ≤ lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) →
    (∀ (lam : ℝ) (hlam : 1 < lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 1 ≤ lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) →
    (∀ (lam : ℝ) (hlam : 1 < lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (lam : ℝ) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A) :
    (1 < lam) ↔ (1 ≤ lam) := by
  omega

set_option maxHeartbeats 200000 in
example (lam : ℝ) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A) :
    (1 < lam) ↔ (1 ≤ lam) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (lam : ℝ) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A) :
    (1 < lam) ↔ (1 ≤ lam) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (lam : ℝ) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A) :
    (1 < lam) ↔ (1 ≤ lam) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (lam : ℝ) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A) :
    (1 < lam) ↔ (1 ≤ lam) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (lam : ℝ) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A) :
    (1 < lam) ↔ (1 ≤ lam) := by
  simp_all

set_option maxHeartbeats 200000 in
example (lam : ℝ) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A) :
    (1 < lam) ↔ (1 ≤ lam) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (1 ≤ lam))) :=
  ⟨(1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (1 ≤ lam))) :=
  ⟨(1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (1 ≤ lam))) :=
  ⟨(0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (1 ≤ lam))) :=
  ⟨(1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (1 ≤ lam))) :=
  ⟨(0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (1 ≤ lam))) :=
  ⟨(2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (1 ≤ lam))) :=
  ⟨(1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (1 ≤ lam))) :=
  ⟨(0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (1 ≤ lam))) :=
  ⟨(2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (1 ≤ lam))) :=
  ⟨(-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (1 ≤ lam))) :=
  ⟨(1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (1 ≤ lam))) :=
  ⟨(0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (1 ≤ lam))) :=
  ⟨(2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (1 ≤ lam))) :=
  ⟨(-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (1 ≤ lam))) :=
  ⟨(1/2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (1 ≤ lam))) :=
  ⟨(1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (1 ≤ lam))) :=
  ⟨(0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (1 ≤ lam))) :=
  ⟨(2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (1 ≤ lam))) :=
  ⟨(-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (1 ≤ lam))) :=
  ⟨(1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (1 ≤ lam))) :=
  ⟨(3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (1 ≤ lam))) :=
  ⟨(0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (1 ≤ lam))) :=
  ⟨(2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (1 ≤ lam))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (1 ≤ lam))) :=
  ⟨(1/2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (1 ≤ lam))) :=
  ⟨(3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (1 ≤ lam))) :=
  ⟨(2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (1 ≤ lam))) :=
  ⟨(-1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (1 ≤ lam))) :=
  ⟨(1/2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (1 ≤ lam))) :=
  ⟨(3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (1 ≤ lam))) :=
  ⟨(-1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (1 ≤ lam))) :=
  ⟨(1/2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), ¬((1 < lam) ↔ (1 ≤ lam)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), ¬((1 < lam) ↔ (1 ≤ lam)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), ¬((1 < lam) ↔ (1 ≤ lam)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), ¬((1 < lam) ↔ (1 ≤ lam)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), ¬((1 < lam) ↔ (1 ≤ lam)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), ¬((1 < lam) ↔ (1 ≤ lam)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (lam : ℝ) (hlam : 1 < lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (lam : ℝ) (hlam : lam > 1) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)

set_option maxHeartbeats 200000 in
example (lam : ℝ) (A : ℝ) :
    (1 < lam) ↔ (lam > 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (lam : ℝ) (A : ℝ) :
    (1 < lam) ↔ (lam > 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (lam : ℝ) (A : ℝ) :
    (1 < lam) ↔ (lam > 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (lam : ℝ) (A : ℝ) :
    (1 < lam) ↔ (lam > 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (lam : ℝ) (A : ℝ) :
    (1 < lam) ↔ (lam > 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (lam : ℝ) (A : ℝ) :
    (1 < lam) ↔ (lam > 1) := by
  omega

set_option maxHeartbeats 200000 in
example (lam : ℝ) (A : ℝ) :
    (1 < lam) ↔ (lam > 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (lam : ℝ) (A : ℝ) :
    (1 < lam) ↔ (lam > 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 1 < lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) ↔
    (∀ (lam : ℝ) (hlam : lam > 1) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 1 < lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) ↔
    (∀ (lam : ℝ) (hlam : lam > 1) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 1 < lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) ↔
    (∀ (lam : ℝ) (hlam : lam > 1) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 1 < lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) ↔
    (∀ (lam : ℝ) (hlam : lam > 1) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (lam : ℝ) (hlam : 1 < lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (lam : ℝ) (hlam₀ : 1 < lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 1 < lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) ↔
    (∀ (lam : ℝ) (hlam₀ : 1 < lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 1 < lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) ↔
    (∀ (lam : ℝ) (hlam₀ : 1 < lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 1 < lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) ↔
    (∀ (lam : ℝ) (hlam₀ : 1 < lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 1 < lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) ↔
    (∀ (lam : ℝ) (hlam₀ : 1 < lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (lam : ℝ) (hlam : 1 < lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (lam : ℝ) (hlam : ¬(lam ≤ 1)) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)

set_option maxHeartbeats 200000 in
example (lam : ℝ) (A : ℝ) :
    (1 < lam) ↔ (¬(lam ≤ 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (lam : ℝ) (A : ℝ) :
    (1 < lam) ↔ (¬(lam ≤ 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (lam : ℝ) (A : ℝ) :
    (1 < lam) ↔ (¬(lam ≤ 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (lam : ℝ) (A : ℝ) :
    (1 < lam) ↔ (¬(lam ≤ 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (lam : ℝ) (A : ℝ) :
    (1 < lam) ↔ (¬(lam ≤ 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (lam : ℝ) (A : ℝ) :
    (1 < lam) ↔ (¬(lam ≤ 1)) := by
  omega

set_option maxHeartbeats 200000 in
example (lam : ℝ) (A : ℝ) :
    (1 < lam) ↔ (¬(lam ≤ 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (lam : ℝ) (A : ℝ) :
    (1 < lam) ↔ (¬(lam ≤ 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 1 < lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) ↔
    (∀ (lam : ℝ) (hlam : ¬(lam ≤ 1)) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 1 < lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) ↔
    (∀ (lam : ℝ) (hlam : ¬(lam ≤ 1)) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 1 < lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) ↔
    (∀ (lam : ℝ) (hlam : ¬(lam ≤ 1)) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : 1 < lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) ↔
    (∀ (lam : ℝ) (hlam : ¬(lam ≤ 1)) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (lam : ℝ) (hlam : 1 < lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (lam : ℝ) (hlam : lam ≥ 1) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : lam ≥ 1) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) →
    (∀ (lam : ℝ) (hlam : 1 < lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : lam ≥ 1) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) →
    (∀ (lam : ℝ) (hlam : 1 < lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : lam ≥ 1) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) →
    (∀ (lam : ℝ) (hlam : 1 < lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : lam ≥ 1) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) →
    (∀ (lam : ℝ) (hlam : 1 < lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : lam ≥ 1) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) →
    (∀ (lam : ℝ) (hlam : 1 < lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : lam ≥ 1) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) →
    (∀ (lam : ℝ) (hlam : 1 < lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (lam : ℝ) (hlam : lam ≥ 1) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) →
    (∀ (lam : ℝ) (hlam : 1 < lam) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A), Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (lam : ℝ) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A) :
    (1 < lam) ↔ (lam ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example (lam : ℝ) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A) :
    (1 < lam) ↔ (lam ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (lam : ℝ) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A) :
    (1 < lam) ↔ (lam ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (lam : ℝ) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A) :
    (1 < lam) ↔ (lam ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (lam : ℝ) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A) :
    (1 < lam) ↔ (lam ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (lam : ℝ) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A) :
    (1 < lam) ↔ (lam ≥ 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example (lam : ℝ) (A : ℝ) (hA : 1 / (lam - 1 - Real.log lam) < A) :
    (1 < lam) ↔ (lam ≥ 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (lam ≥ 1))) :=
  ⟨(1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (lam ≥ 1))) :=
  ⟨(1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (lam ≥ 1))) :=
  ⟨(0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (lam ≥ 1))) :=
  ⟨(1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (lam ≥ 1))) :=
  ⟨(0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (lam ≥ 1))) :=
  ⟨(2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (lam ≥ 1))) :=
  ⟨(1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (lam ≥ 1))) :=
  ⟨(0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (lam ≥ 1))) :=
  ⟨(2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (lam ≥ 1))) :=
  ⟨(-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (lam ≥ 1))) :=
  ⟨(1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (lam ≥ 1))) :=
  ⟨(0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (lam ≥ 1))) :=
  ⟨(2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (lam ≥ 1))) :=
  ⟨(-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (lam ≥ 1))) :=
  ⟨(1/2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (lam ≥ 1))) :=
  ⟨(1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (lam ≥ 1))) :=
  ⟨(0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (lam ≥ 1))) :=
  ⟨(2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (lam ≥ 1))) :=
  ⟨(-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (lam ≥ 1))) :=
  ⟨(1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (lam ≥ 1))) :=
  ⟨(3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (lam ≥ 1))) :=
  ⟨(0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (lam ≥ 1))) :=
  ⟨(2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (lam ≥ 1))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (lam ≥ 1))) :=
  ⟨(1/2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (lam ≥ 1))) :=
  ⟨(3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (lam ≥ 1))) :=
  ⟨(2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (lam ≥ 1))) :=
  ⟨(-1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (lam ≥ 1))) :=
  ⟨(1/2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (lam ≥ 1))) :=
  ⟨(3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (lam ≥ 1))) :=
  ⟨(-1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ) (A : ℝ), (1 / (lam - 1 - Real.log lam) < A) ∧ (¬((1 < lam) ↔ (lam ≥ 1))) :=
  ⟨(1/2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), ¬((1 < lam) ↔ (lam ≥ 1)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), ¬((1 < lam) ↔ (lam ≥ 1)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), ¬((1 < lam) ↔ (lam ≥ 1)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), ¬((1 < lam) ↔ (lam ≥ 1)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), ¬((1 < lam) ↔ (lam ≥ 1)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (lam : ℝ), ¬((1 < lam) ↔ (lam ≥ 1)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (lam : ℝ) (A : ℝ) (hlam : 1 < lam) (hA : 1 / (lam - 1 - Real.log lam) < A) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (lam : ℝ) (A : ℝ) (hlam : 1 < lam) (hA : 1 / (lam - 1 - Real.log lam) < A) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (lam : ℝ) (A : ℝ) (hlam : 1 < lam) (hA : 1 / (lam - 1 - Real.log lam) < A) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (lam : ℝ) (A : ℝ) (hlam : 1 < lam) (hA : 1 / (lam - 1 - Real.log lam) < A) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (lam : ℝ) (A : ℝ) (hlam : 1 < lam) (hA : 1 / (lam - 1 - Real.log lam) < A) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
