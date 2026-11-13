import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 150

*References:*
- [erdosproblems.com/150](https://www.erdosproblems.com/150)
- [Br24] Bradač, D., *On a question of Erdős and Nešetřil about minimal cuts in a graph*.
  arXiv:2409.02974 (2024).
- [Er88] Erdős, P., *Problems and results in combinatorial analysis and graph theory*.
  Discrete Math. (1988), 81-92.
- [FKTV08] Fomin, Fedor V. and Kratsch, Dieter and Todinca, Ioan and Villanger, Yngve, *Exact
  algorithms for treewidth and minimum fill-in*. SIAM J. Comput. (2008), 1058-1079.
- [FoVi12] Fomin, Fedor V. and Villanger, Yngve, *Treewidth computation and extremal
  combinatorics*. Combinatorica (2012), 289-308.
- [GaMa18] Gaspers, Serge and Mackenzie, Simon, *On the number of minimal separators in graphs*.
  J. Graph Theory (2018), 653-659.
-/

section

open Filter

open scoped Topology

namespace Erdos150

/-- A *minimal cut* of a graph `G` is a minimal set `T` of vertices whose removal disconnects
`G`, that is, `G - T` fails to be preconnected while `G - S` is preconnected for every `S ⊂ T`. -/
def IsMinimalCut {V : Type*} (G : SimpleGraph V) (T : Set V) : Prop :=
  ¬ (G.induce Tᶜ).Preconnected ∧ ∀ S ⊂ T, (G.induce Sᶜ).Preconnected

/-- The maximum number $c(n)$ of minimal cuts a graph on $n$ vertices can have. -/
noncomputable def maxMinimalCuts (n : ℕ) : ℕ :=
  sSup {k | ∃ G : SimpleGraph (Fin n), {T : Set (Fin n) | IsMinimalCut G T}.ncard = k}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 < α

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 < α) →
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 < α) →
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 < α) →
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 < α) →
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 < α) →
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 < α) →
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 < α) →
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)) ∧ (¬(1.4457 < α)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)) ∧ (¬(1.4457 < α)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)) ∧ (¬(1.4457 < α)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)) ∧ (¬(1.4457 < α)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)) ∧ (¬(1.4457 < α)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)) ∧ (¬(1.4457 < α)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((1.4457 ≤ α) ↔ (1.4457 < α)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((1.4457 ≤ α) ↔ (1.4457 < α)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((1.4457 ≤ α) ↔ (1.4457 < α)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((1.4457 ≤ α) ↔ (1.4457 < α)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((1.4457 ≤ α) ↔ (1.4457 < α)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((1.4457 ≤ α) ↔ (1.4457 < α)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≥ α

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≥ α) →
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≥ α) →
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≥ α) →
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≥ α) →
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≥ α) →
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≥ α) →
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≥ α) →
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) →
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≥ α) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) →
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≥ α) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) →
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≥ α) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) →
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≥ α) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) →
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≥ α) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) →
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≥ α) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) →
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≥ α) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)) ∧ (¬(1.4457 ≥ α)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)) ∧ (¬(1.4457 ≥ α)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)) ∧ (¬(1.4457 ≥ α)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)) ∧ (¬(1.4457 ≥ α)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)) ∧ (¬(1.4457 ≥ α)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)) ∧ (¬(1.4457 ≥ α)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((1.4457 ≤ α) ↔ (1.4457 ≥ α)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((1.4457 ≤ α) ↔ (1.4457 ≥ α)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((1.4457 ≤ α) ↔ (1.4457 ≥ α)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((1.4457 ≤ α) ↔ (1.4457 ≥ α)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((1.4457 ≤ α) ↔ (1.4457 ≥ α)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((1.4457 ≤ α) ↔ (1.4457 ≥ α)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), α ≥ 1.4457

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (1.4457 ≤ α) ↔ (α ≥ 1.4457) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (1.4457 ≤ α) ↔ (α ≥ 1.4457) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (1.4457 ≤ α) ↔ (α ≥ 1.4457) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (1.4457 ≤ α) ↔ (α ≥ 1.4457) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (1.4457 ≤ α) ↔ (α ≥ 1.4457) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (1.4457 ≤ α) ↔ (α ≥ 1.4457) := by
  omega

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (1.4457 ≤ α) ↔ (α ≥ 1.4457) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (1.4457 ≤ α) ↔ (α ≥ 1.4457) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) ↔
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), α ≥ 1.4457) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) ↔
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), α ≥ 1.4457) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) ↔
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), α ≥ 1.4457) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) ↔
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), α ≥ 1.4457) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα₀ : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) ↔
    (∀ (α : ℝ) (hα₀ : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) ↔
    (∀ (α : ℝ) (hα₀ : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) ↔
    (∀ (α : ℝ) (hα₀ : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) ↔
    (∀ (α : ℝ) (hα₀ : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), ¬(α < 1.4457)

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (1.4457 ≤ α) ↔ (¬(α < 1.4457)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (1.4457 ≤ α) ↔ (¬(α < 1.4457)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (1.4457 ≤ α) ↔ (¬(α < 1.4457)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (1.4457 ≤ α) ↔ (¬(α < 1.4457)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (1.4457 ≤ α) ↔ (¬(α < 1.4457)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (1.4457 ≤ α) ↔ (¬(α < 1.4457)) := by
  omega

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (1.4457 ≤ α) ↔ (¬(α < 1.4457)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (1.4457 ≤ α) ↔ (¬(α < 1.4457)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) ↔
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), ¬(α < 1.4457)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) ↔
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), ¬(α < 1.4457)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) ↔
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), ¬(α < 1.4457)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) ↔
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), ¬(α < 1.4457)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), α > 1.4457

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), α > 1.4457) →
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), α > 1.4457) →
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), α > 1.4457) →
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), α > 1.4457) →
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), α > 1.4457) →
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), α > 1.4457) →
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), α > 1.4457) →
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)) ∧ (¬(α > 1.4457)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)) ∧ (¬(α > 1.4457)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)) ∧ (¬(α > 1.4457)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)) ∧ (¬(α > 1.4457)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)) ∧ (¬(α > 1.4457)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)) ∧ (¬(α > 1.4457)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((1.4457 ≤ α) ↔ (α > 1.4457)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((1.4457 ≤ α) ↔ (α > 1.4457)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((1.4457 ≤ α) ↔ (α > 1.4457)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((1.4457 ≤ α) ↔ (α > 1.4457)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((1.4457 ≤ α) ↔ (α > 1.4457)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((1.4457 ≤ α) ↔ (α > 1.4457)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), α ≤ 1.4457

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), α ≤ 1.4457) →
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), α ≤ 1.4457) →
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), α ≤ 1.4457) →
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), α ≤ 1.4457) →
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), α ≤ 1.4457) →
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), α ≤ 1.4457) →
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), α ≤ 1.4457) →
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) →
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), α ≤ 1.4457) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) →
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), α ≤ 1.4457) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) →
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), α ≤ 1.4457) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) →
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), α ≤ 1.4457) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) →
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), α ≤ 1.4457) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) →
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), α ≤ 1.4457) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), 1.4457 ≤ α) →
    (∀ (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)), α ≤ 1.4457) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)) ∧ (¬(α ≤ 1.4457)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)) ∧ (¬(α ≤ 1.4457)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)) ∧ (¬(α ≤ 1.4457)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)) ∧ (¬(α ≤ 1.4457)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)) ∧ (¬(α ≤ 1.4457)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)) ∧ (¬(α ≤ 1.4457)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((1.4457 ≤ α) ↔ (α ≤ 1.4457)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((1.4457 ≤ α) ↔ (α ≤ 1.4457)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((1.4457 ≤ α) ↔ (α ≤ 1.4457)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((1.4457 ≤ α) ↔ (α ≤ 1.4457)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((1.4457 ≤ α) ↔ (α ≤ 1.4457)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((1.4457 ≤ α) ↔ (α ≤ 1.4457)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα : Tendsto (fun n : ℕ ↦ (maxMinimalCuts n : ℝ) ^ (1 / n : ℝ)) atTop (𝓝 α)) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
