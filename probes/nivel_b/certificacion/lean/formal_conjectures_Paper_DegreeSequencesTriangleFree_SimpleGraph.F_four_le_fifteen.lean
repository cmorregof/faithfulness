import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Degrees
/-!
Title: Degree sequences in triangle-free graphs
Authors: P. Erdős, S. Fajtlowicz and W. Staton,
Published in Discrete Mathematics 92 (1991) 85–88.
-/

section

open BigOperators
open scoped Finset

namespace DegreeSequencesTriangleFree

/-- A sequence of natural numbers is **compact** on a set `S` if consecutive terms at distance
`2` differ by `1` for all `k ∈ S`. -/
def IsCompactSequenceOn (d : ℕ → ℕ) (S : Set ℕ) : Prop :=
  ∀ k ∈ S, d (k + 2) = d k + 1

end DegreeSequencesTriangleFree

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The number of vertices of `G` having degree `d`. -/
noncomputable def degreeFreq (G : SimpleGraph α) (d : ℕ) : ℕ :=
  open scoped Classical in
  #{v | G.degree v = d}

end SimpleGraph

namespace DegreeSequencesTriangleFree

variable (d : ℕ → ℕ) (n k r : ℕ)

end DegreeSequencesTriangleFree

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The degree sequence of `G` is **compact** if it satisfies
`IsCompactSequenceOn` for all valid indices `k` such that `k + 2 < Fintype.card α`. -/
def HasCompactdegreeSequence (G : SimpleGraph α) [DecidableRel G.Adj] : Prop :=
  DegreeSequencesTriangleFree.IsCompactSequenceOn (fun k => (degreeSequence G).getD k 0) {k | k + 2 < Fintype.card α}

/-- `F n` is the smallest number of vertices of a triangle-free graph
with chromatic number `n` and `f = 3`. -/
noncomputable def F (n : ℕ) : ℕ :=
  sInf { p | ∃ (G : SimpleGraph (Fin p)) (_ : DecidableRel G.Adj),
    G.CliqueFree 3 ∧ G.chromaticNumber = n ∧ degreeSequenceMultiplicity G = 3 }

set_option maxHeartbeats 200000 in
example : Prop :=
  F 4 ≤ 15

set_option maxHeartbeats 200000 in
example : Prop :=
  F 4 < 15

set_option maxHeartbeats 200000 in
example :
    (F 4 < 15) →
    (F 4 ≤ 15) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (F 4 < 15) →
    (F 4 ≤ 15) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (F 4 < 15) →
    (F 4 ≤ 15) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (F 4 < 15) →
    (F 4 ≤ 15) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (F 4 < 15) →
    (F 4 ≤ 15) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (F 4 < 15) →
    (F 4 ≤ 15) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (F 4 < 15) →
    (F 4 ≤ 15) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (¬(F 4 < 15)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (¬(F 4 < 15)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((F 4 ≤ 15) ↔ (F 4 < 15)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((F 4 ≤ 15) ↔ (F 4 < 15)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  F 4 ≤ 15

set_option maxHeartbeats 200000 in
example : Prop :=
  F 5 ≤ 15

set_option maxHeartbeats 200000 in
example :
    (F 5 ≤ 15) →
    (F 4 ≤ 15) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (F 5 ≤ 15) →
    (F 4 ≤ 15) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (F 5 ≤ 15) →
    (F 4 ≤ 15) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (F 5 ≤ 15) →
    (F 4 ≤ 15) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (F 5 ≤ 15) →
    (F 4 ≤ 15) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (F 5 ≤ 15) →
    (F 4 ≤ 15) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (F 5 ≤ 15) →
    (F 4 ≤ 15) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (F 4 ≤ 15) →
    (F 5 ≤ 15) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (F 4 ≤ 15) →
    (F 5 ≤ 15) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (F 4 ≤ 15) →
    (F 5 ≤ 15) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (F 4 ≤ 15) →
    (F 5 ≤ 15) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (F 4 ≤ 15) →
    (F 5 ≤ 15) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (F 4 ≤ 15) →
    (F 5 ≤ 15) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (F 4 ≤ 15) →
    (F 5 ≤ 15) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (¬(F 5 ≤ 15)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (¬(F 5 ≤ 15)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((F 4 ≤ 15) ↔ (F 5 ≤ 15)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((F 4 ≤ 15) ↔ (F 5 ≤ 15)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  F 4 ≤ 15

set_option maxHeartbeats 200000 in
example : Prop :=
  F 4 ≥ 15

set_option maxHeartbeats 200000 in
example :
    (F 4 ≥ 15) →
    (F 4 ≤ 15) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (F 4 ≥ 15) →
    (F 4 ≤ 15) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (F 4 ≥ 15) →
    (F 4 ≤ 15) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (F 4 ≥ 15) →
    (F 4 ≤ 15) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (F 4 ≥ 15) →
    (F 4 ≤ 15) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (F 4 ≥ 15) →
    (F 4 ≤ 15) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (F 4 ≥ 15) →
    (F 4 ≤ 15) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (F 4 ≤ 15) →
    (F 4 ≥ 15) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (F 4 ≤ 15) →
    (F 4 ≥ 15) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (F 4 ≤ 15) →
    (F 4 ≥ 15) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (F 4 ≤ 15) →
    (F 4 ≥ 15) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (F 4 ≤ 15) →
    (F 4 ≥ 15) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (F 4 ≤ 15) →
    (F 4 ≥ 15) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (F 4 ≤ 15) →
    (F 4 ≥ 15) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (¬(F 4 ≥ 15)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (¬(F 4 ≥ 15)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((F 4 ≤ 15) ↔ (F 4 ≥ 15)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((F 4 ≤ 15) ↔ (F 4 ≥ 15)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  F 4 ≤ 15

set_option maxHeartbeats 200000 in
example : Prop :=
  15 ≥ F 4

set_option maxHeartbeats 200000 in
example  :
    (F 4 ≤ 15) ↔ (15 ≥ F 4) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example  :
    (F 4 ≤ 15) ↔ (15 ≥ F 4) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example  :
    (F 4 ≤ 15) ↔ (15 ≥ F 4) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example  :
    (F 4 ≤ 15) ↔ (15 ≥ F 4) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example  :
    (F 4 ≤ 15) ↔ (15 ≥ F 4) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example  :
    (F 4 ≤ 15) ↔ (15 ≥ F 4) := by
  omega

set_option maxHeartbeats 200000 in
example  :
    (F 4 ≤ 15) ↔ (15 ≥ F 4) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example  :
    (F 4 ≤ 15) ↔ (15 ≥ F 4) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (F 4 ≤ 15) ↔
    (15 ≥ F 4) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (F 4 ≤ 15) ↔
    (15 ≥ F 4) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (F 4 ≤ 15) ↔
    (15 ≥ F 4) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (F 4 ≤ 15) ↔
    (15 ≥ F 4) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  F 4 ≤ 15

set_option maxHeartbeats 200000 in
example : Prop :=
  ¬(15 < F 4)

set_option maxHeartbeats 200000 in
example  :
    (F 4 ≤ 15) ↔ (¬(15 < F 4)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example  :
    (F 4 ≤ 15) ↔ (¬(15 < F 4)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example  :
    (F 4 ≤ 15) ↔ (¬(15 < F 4)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example  :
    (F 4 ≤ 15) ↔ (¬(15 < F 4)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example  :
    (F 4 ≤ 15) ↔ (¬(15 < F 4)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example  :
    (F 4 ≤ 15) ↔ (¬(15 < F 4)) := by
  omega

set_option maxHeartbeats 200000 in
example  :
    (F 4 ≤ 15) ↔ (¬(15 < F 4)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example  :
    (F 4 ≤ 15) ↔ (¬(15 < F 4)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (F 4 ≤ 15) ↔
    (¬(15 < F 4)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (F 4 ≤ 15) ↔
    (¬(15 < F 4)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (F 4 ≤ 15) ↔
    (¬(15 < F 4)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (F 4 ≤ 15) ↔
    (¬(15 < F 4)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  F 4 ≤ 15

set_option maxHeartbeats 200000 in
example : Prop :=
  15 > F 4

set_option maxHeartbeats 200000 in
example :
    (15 > F 4) →
    (F 4 ≤ 15) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (15 > F 4) →
    (F 4 ≤ 15) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (15 > F 4) →
    (F 4 ≤ 15) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (15 > F 4) →
    (F 4 ≤ 15) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (15 > F 4) →
    (F 4 ≤ 15) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (15 > F 4) →
    (F 4 ≤ 15) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (15 > F 4) →
    (F 4 ≤ 15) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (¬(15 > F 4)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (¬(15 > F 4)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((F 4 ≤ 15) ↔ (15 > F 4)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((F 4 ≤ 15) ↔ (15 > F 4)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  F 4 ≤ 15

set_option maxHeartbeats 200000 in
example : Prop :=
  16 ≥ F 4

set_option maxHeartbeats 200000 in
example :
    (F 4 ≤ 15) →
    (16 ≥ F 4) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (F 4 ≤ 15) →
    (16 ≥ F 4) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (F 4 ≤ 15) →
    (16 ≥ F 4) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (F 4 ≤ 15) →
    (16 ≥ F 4) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (F 4 ≤ 15) →
    (16 ≥ F 4) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (F 4 ≤ 15) →
    (16 ≥ F 4) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (F 4 ≤ 15) →
    (16 ≥ F 4) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (¬(16 ≥ F 4)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (¬(16 ≥ F 4)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((F 4 ≤ 15) ↔ (16 ≥ F 4)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((F 4 ≤ 15) ↔ (16 ≥ F 4)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  F 4 ≤ 15

set_option maxHeartbeats 200000 in
example : Prop :=
  15 ≤ F 4

set_option maxHeartbeats 200000 in
example :
    (15 ≤ F 4) →
    (F 4 ≤ 15) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (15 ≤ F 4) →
    (F 4 ≤ 15) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (15 ≤ F 4) →
    (F 4 ≤ 15) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (15 ≤ F 4) →
    (F 4 ≤ 15) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (15 ≤ F 4) →
    (F 4 ≤ 15) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (15 ≤ F 4) →
    (F 4 ≤ 15) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (15 ≤ F 4) →
    (F 4 ≤ 15) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (F 4 ≤ 15) →
    (15 ≤ F 4) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (F 4 ≤ 15) →
    (15 ≤ F 4) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (F 4 ≤ 15) →
    (15 ≤ F 4) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (F 4 ≤ 15) →
    (15 ≤ F 4) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (F 4 ≤ 15) →
    (15 ≤ F 4) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (F 4 ≤ 15) →
    (15 ≤ F 4) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (F 4 ≤ 15) →
    (15 ≤ F 4) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (¬(15 ≤ F 4)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (¬(15 ≤ F 4)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((F 4 ≤ 15) ↔ (15 ≤ F 4)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((F 4 ≤ 15) ↔ (15 ≤ F 4)) :=
  by decide

#eval "FIN_CERTIFICAR"
