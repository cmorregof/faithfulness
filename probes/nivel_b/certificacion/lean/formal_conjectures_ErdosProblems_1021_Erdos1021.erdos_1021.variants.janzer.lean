import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 1021

*References:*
- [erdosproblems.com/1021](https://www.erdosproblems.com/1021)
- [Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
- [Er74c] Erdős, Paul, *Extremal problems on graphs and hypergraphs*. (1974), 75-84.
- [CoLe21] Conlon, David and Lee, Joonkyung, *On the extremal number of subdivisions*. Int. Math.
  Res. Not. IMRN (2021), 9122--9145.
- [Ja19] Janzer, Oliver, *Improved bounds for the extremal number of subdivisions*. Electron. J.
  Combin. (2019), Paper No. 3.3, 6.
-/

section

open Filter Asymptotics

namespace Erdos1021

/-- The graph `G_k`: the bipartite graph between `{y_1, …, y_k}` (the elements of `Fin k`) and
`{z_1, …, z_{k choose 2}}` (the two-element subsets of `Fin k`), each `z` being joined to the two
elements of the corresponding pair. This is the `1`-subdivision of `K_k`. -/
def cliqueSubdivision (k : ℕ) : SimpleGraph (Fin k ⊕ Set.powersetCard (Fin k) 2) where
  Adj x y :=
    match x, y with
    | Sum.inl i, Sum.inr p => i ∈ (p : Finset (Fin k))
    | Sum.inr p, Sum.inl i => i ∈ (p : Finset (Fin k))
    | _, _ => False
  symm := by
    constructor
    intro x y h
    cases x <;> cases y <;> simp_all
  loopless := by
    constructor
    intro x
    cases x <;> simp

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6))

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6))) →
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6))) →
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6))) →
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6))) →
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6))) →
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6))) →
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6))) →
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) →
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) →
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) →
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) →
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) →
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) →
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) →
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬(((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) ↔ ((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬(((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) ↔ ((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬(((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) ↔ ((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬(((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) ↔ ((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬(((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) ↔ ((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬(((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) ↔ ((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬(((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) ↔ ((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬(((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) ↔ ((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬(((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) ↔ ((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 3), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (k ≥ 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (k ≥ 3) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (k ≥ 3) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (k ≥ 3) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (k ≥ 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (k ≥ 3) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (k ≥ 3) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (k ≥ 3) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) ↔
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) ↔
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) ↔
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) ↔
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk₀ : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) ↔
    (∀ (k : ℕ) (hk₀ : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) ↔
    (∀ (k : ℕ) (hk₀ : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) ↔
    (∀ (k : ℕ) (hk₀ : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) ↔
    (∀ (k : ℕ) (hk₀ : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : ¬(k < 3)), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (¬(k < 3)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (¬(k < 3)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (¬(k < 3)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (¬(k < 3)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (¬(k < 3)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (¬(k < 3)) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (¬(k < 3)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (¬(k < 3)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) ↔
    (∀ (k : ℕ) (hk : ¬(k < 3)), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) ↔
    (∀ (k : ℕ) (hk : ¬(k < 3)), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) ↔
    (∀ (k : ℕ) (hk : ¬(k < 3)), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) ↔
    (∀ (k : ℕ) (hk : ¬(k < 3)), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 < k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (2 < k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (2 < k) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (2 < k) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (2 < k) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (2 < k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (2 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (2 < k) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (3 ≤ k) ↔ (2 < k) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) ↔
    (∀ (k : ℕ) (hk : 2 < k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) ↔
    (∀ (k : ℕ) (hk : 2 < k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) ↔
    (∀ (k : ℕ) (hk : 2 < k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) ↔
    (∀ (k : ℕ) (hk : 2 < k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 3), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6))

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6))) →
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6))) →
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6))) →
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6))) →
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6))) →
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6))) →
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6))) →
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) →
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) →
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) →
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) →
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) →
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) →
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) →
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬(((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) ↔ ((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬(((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) ↔ ((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬(((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) ↔ ((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬(((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) ↔ ((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬(((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) ↔ ((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬(((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) ↔ ((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬(((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) ↔ ((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬(((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) ↔ ((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬(((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) ↔ ((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 < k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6))

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 < k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6))) →
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 < k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6))) →
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 < k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6))) →
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 < k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6))) →
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 < k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6))) →
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 < k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6))) →
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 < k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6))) →
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) →
    (∀ (k : ℕ) (hk : 2 < k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) →
    (∀ (k : ℕ) (hk : 2 < k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) →
    (∀ (k : ℕ) (hk : 2 < k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) →
    (∀ (k : ℕ) (hk : 2 < k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) →
    (∀ (k : ℕ) (hk : 2 < k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) →
    (∀ (k : ℕ) (hk : 2 < k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) →
    (∀ (k : ℕ) (hk : 2 < k), (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (3 ≤ k) ∧ (¬((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬(((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) ↔ ((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬(((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) ↔ ((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬(((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) ↔ ((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬(((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) ↔ ((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬(((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) ↔ ((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬(((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) ↔ ((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬(((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) ↔ ((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬(((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) ↔ ((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬(((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (4 * (k : ℝ) - 6))) ↔ ((fun n : ℕ ↦ (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 - 1 / (5 * (k : ℝ) - 6)))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 3 ≤ k) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 3 ≤ k) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 3 ≤ k) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 3 ≤ k) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 3 ≤ k) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
