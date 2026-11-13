import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

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

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 < d (k + 2) - d k

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 < d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 < d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 < d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 < d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 < d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 < d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 < d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (Monotone d) ∧ (∀ k, d (k + 2) ≠ d k) ∧ (¬(1 < d (k + 2) - d k)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (Monotone d) ∧ (∀ k, d (k + 2) ≠ d k) ∧ (¬(1 < d (k + 2) - d k)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((1 ≤ d (k + 2) - d k) ↔ (1 < d (k + 2) - d k)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((1 ≤ d (k + 2) - d k) ↔ (1 < d (k + 2) - d k)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 3) ≠ d k), 1 ≤ d (k + 2) - d k

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 3) ≠ d k), 1 ≤ d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 3) ≠ d k), 1 ≤ d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 3) ≠ d k), 1 ≤ d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 3) ≠ d k), 1 ≤ d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 3) ≠ d k), 1 ≤ d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 3) ≠ d k), 1 ≤ d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 3) ≠ d k), 1 ≤ d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 3) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 3) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 3) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 3) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 3) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 3) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 3) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example  (h_mono : Monotone d) :
    (∀ k, d (k + 2) ≠ d k) ↔ (∀ k, d (k + 3) ≠ d k) := by
  omega

set_option maxHeartbeats 200000 in
example  (h_mono : Monotone d) :
    (∀ k, d (k + 2) ≠ d k) ↔ (∀ k, d (k + 3) ≠ d k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example  (h_mono : Monotone d) :
    (∀ k, d (k + 2) ≠ d k) ↔ (∀ k, d (k + 3) ≠ d k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example  (h_mono : Monotone d) :
    (∀ k, d (k + 2) ≠ d k) ↔ (∀ k, d (k + 3) ≠ d k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example  (h_mono : Monotone d) :
    (∀ k, d (k + 2) ≠ d k) ↔ (∀ k, d (k + 3) ≠ d k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example  (h_mono : Monotone d) :
    (∀ k, d (k + 2) ≠ d k) ↔ (∀ k, d (k + 3) ≠ d k) := by
  simp_all

set_option maxHeartbeats 200000 in
example  (h_mono : Monotone d) :
    (∀ k, d (k + 2) ≠ d k) ↔ (∀ k, d (k + 3) ≠ d k) := by
  plausible

set_option maxHeartbeats 200000 in
example : (Monotone d) ∧ (¬((∀ k, d (k + 2) ≠ d k) ↔ (∀ k, d (k + 3) ≠ d k))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (Monotone d) ∧ (¬((∀ k, d (k + 2) ≠ d k) ↔ (∀ k, d (k + 3) ≠ d k))) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((∀ k, d (k + 2) ≠ d k) ↔ (∀ k, d (k + 3) ≠ d k)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((∀ k, d (k + 2) ≠ d k) ↔ (∀ k, d (k + 3) ≠ d k)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≥ d (k + 2) - d k

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≥ d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≥ d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≥ d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≥ d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≥ d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≥ d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≥ d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≥ d (k + 2) - d k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≥ d (k + 2) - d k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≥ d (k + 2) - d k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≥ d (k + 2) - d k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≥ d (k + 2) - d k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≥ d (k + 2) - d k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≥ d (k + 2) - d k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (Monotone d) ∧ (∀ k, d (k + 2) ≠ d k) ∧ (¬(1 ≥ d (k + 2) - d k)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (Monotone d) ∧ (∀ k, d (k + 2) ≠ d k) ∧ (¬(1 ≥ d (k + 2) - d k)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((1 ≤ d (k + 2) - d k) ↔ (1 ≥ d (k + 2) - d k)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((1 ≤ d (k + 2) - d k) ↔ (1 ≥ d (k + 2) - d k)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), d (k + 2) - d k ≥ 1

set_option maxHeartbeats 200000 in
example  :
    (1 ≤ d (k + 2) - d k) ↔ (d (k + 2) - d k ≥ 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example  :
    (1 ≤ d (k + 2) - d k) ↔ (d (k + 2) - d k ≥ 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example  :
    (1 ≤ d (k + 2) - d k) ↔ (d (k + 2) - d k ≥ 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example  :
    (1 ≤ d (k + 2) - d k) ↔ (d (k + 2) - d k ≥ 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example  :
    (1 ≤ d (k + 2) - d k) ↔ (d (k + 2) - d k ≥ 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example  :
    (1 ≤ d (k + 2) - d k) ↔ (d (k + 2) - d k ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example  :
    (1 ≤ d (k + 2) - d k) ↔ (d (k + 2) - d k ≥ 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example  :
    (1 ≤ d (k + 2) - d k) ↔ (d (k + 2) - d k ≥ 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) ↔
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), d (k + 2) - d k ≥ 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) ↔
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), d (k + 2) - d k ≥ 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) ↔
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), d (k + 2) - d k ≥ 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) ↔
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), d (k + 2) - d k ≥ 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h_no_three : ∀ k, d (k + 2) ≠ d k) (h_mono : Monotone d), 1 ≤ d (k + 2) - d k

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) ↔
    (∀ (h_no_three : ∀ k, d (k + 2) ≠ d k) (h_mono : Monotone d), 1 ≤ d (k + 2) - d k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) ↔
    (∀ (h_no_three : ∀ k, d (k + 2) ≠ d k) (h_mono : Monotone d), 1 ≤ d (k + 2) - d k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) ↔
    (∀ (h_no_three : ∀ k, d (k + 2) ≠ d k) (h_mono : Monotone d), 1 ≤ d (k + 2) - d k) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) ↔
    (∀ (h_no_three : ∀ k, d (k + 2) ≠ d k) (h_mono : Monotone d), 1 ≤ d (k + 2) - d k) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h_mono₀ : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) ↔
    (∀ (h_mono₀ : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) ↔
    (∀ (h_mono₀ : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) ↔
    (∀ (h_mono₀ : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) ↔
    (∀ (h_mono₀ : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), ¬(d (k + 2) - d k < 1)

set_option maxHeartbeats 200000 in
example  :
    (1 ≤ d (k + 2) - d k) ↔ (¬(d (k + 2) - d k < 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example  :
    (1 ≤ d (k + 2) - d k) ↔ (¬(d (k + 2) - d k < 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example  :
    (1 ≤ d (k + 2) - d k) ↔ (¬(d (k + 2) - d k < 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example  :
    (1 ≤ d (k + 2) - d k) ↔ (¬(d (k + 2) - d k < 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example  :
    (1 ≤ d (k + 2) - d k) ↔ (¬(d (k + 2) - d k < 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example  :
    (1 ≤ d (k + 2) - d k) ↔ (¬(d (k + 2) - d k < 1)) := by
  omega

set_option maxHeartbeats 200000 in
example  :
    (1 ≤ d (k + 2) - d k) ↔ (¬(d (k + 2) - d k < 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example  :
    (1 ≤ d (k + 2) - d k) ↔ (¬(d (k + 2) - d k < 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) ↔
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), ¬(d (k + 2) - d k < 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) ↔
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), ¬(d (k + 2) - d k < 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) ↔
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), ¬(d (k + 2) - d k < 1)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) ↔
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), ¬(d (k + 2) - d k < 1)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), d (k + 2) - d k > 1

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), d (k + 2) - d k > 1) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), d (k + 2) - d k > 1) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), d (k + 2) - d k > 1) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), d (k + 2) - d k > 1) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), d (k + 2) - d k > 1) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), d (k + 2) - d k > 1) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), d (k + 2) - d k > 1) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (Monotone d) ∧ (∀ k, d (k + 2) ≠ d k) ∧ (¬(d (k + 2) - d k > 1)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (Monotone d) ∧ (∀ k, d (k + 2) ≠ d k) ∧ (¬(d (k + 2) - d k > 1)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((1 ≤ d (k + 2) - d k) ↔ (d (k + 2) - d k > 1)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((1 ≤ d (k + 2) - d k) ↔ (d (k + 2) - d k > 1)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 3) ≠ d k), d (k + 2) - d k ≥ 1

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 3) ≠ d k), d (k + 2) - d k ≥ 1) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 3) ≠ d k), d (k + 2) - d k ≥ 1) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 3) ≠ d k), d (k + 2) - d k ≥ 1) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 3) ≠ d k), d (k + 2) - d k ≥ 1) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 3) ≠ d k), d (k + 2) - d k ≥ 1) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 3) ≠ d k), d (k + 2) - d k ≥ 1) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 3) ≠ d k), d (k + 2) - d k ≥ 1) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 3) ≠ d k), d (k + 2) - d k ≥ 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 3) ≠ d k), d (k + 2) - d k ≥ 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 3) ≠ d k), d (k + 2) - d k ≥ 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 3) ≠ d k), d (k + 2) - d k ≥ 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 3) ≠ d k), d (k + 2) - d k ≥ 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 3) ≠ d k), d (k + 2) - d k ≥ 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 3) ≠ d k), d (k + 2) - d k ≥ 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example  (h_mono : Monotone d) :
    (∀ k, d (k + 2) ≠ d k) ↔ (∀ k, d (k + 3) ≠ d k) := by
  omega

set_option maxHeartbeats 200000 in
example  (h_mono : Monotone d) :
    (∀ k, d (k + 2) ≠ d k) ↔ (∀ k, d (k + 3) ≠ d k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example  (h_mono : Monotone d) :
    (∀ k, d (k + 2) ≠ d k) ↔ (∀ k, d (k + 3) ≠ d k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example  (h_mono : Monotone d) :
    (∀ k, d (k + 2) ≠ d k) ↔ (∀ k, d (k + 3) ≠ d k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example  (h_mono : Monotone d) :
    (∀ k, d (k + 2) ≠ d k) ↔ (∀ k, d (k + 3) ≠ d k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example  (h_mono : Monotone d) :
    (∀ k, d (k + 2) ≠ d k) ↔ (∀ k, d (k + 3) ≠ d k) := by
  simp_all

set_option maxHeartbeats 200000 in
example  (h_mono : Monotone d) :
    (∀ k, d (k + 2) ≠ d k) ↔ (∀ k, d (k + 3) ≠ d k) := by
  plausible

set_option maxHeartbeats 200000 in
example : (Monotone d) ∧ (¬((∀ k, d (k + 2) ≠ d k) ↔ (∀ k, d (k + 3) ≠ d k))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (Monotone d) ∧ (¬((∀ k, d (k + 2) ≠ d k) ↔ (∀ k, d (k + 3) ≠ d k))) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((∀ k, d (k + 2) ≠ d k) ↔ (∀ k, d (k + 3) ≠ d k)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((∀ k, d (k + 2) ≠ d k) ↔ (∀ k, d (k + 3) ≠ d k)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), d (k + 2) - d k ≤ 1

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), d (k + 2) - d k ≤ 1) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), d (k + 2) - d k ≤ 1) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), d (k + 2) - d k ≤ 1) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), d (k + 2) - d k ≤ 1) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), d (k + 2) - d k ≤ 1) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), d (k + 2) - d k ≤ 1) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), d (k + 2) - d k ≤ 1) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), d (k + 2) - d k ≤ 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), d (k + 2) - d k ≤ 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), d (k + 2) - d k ≤ 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), d (k + 2) - d k ≤ 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), d (k + 2) - d k ≤ 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), d (k + 2) - d k ≤ 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), 1 ≤ d (k + 2) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k), d (k + 2) - d k ≤ 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (Monotone d) ∧ (∀ k, d (k + 2) ≠ d k) ∧ (¬(d (k + 2) - d k ≤ 1)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (Monotone d) ∧ (∀ k, d (k + 2) ≠ d k) ∧ (¬(d (k + 2) - d k ≤ 1)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((1 ≤ d (k + 2) - d k) ↔ (d (k + 2) - d k ≤ 1)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((1 ≤ d (k + 2) - d k) ↔ (d (k + 2) - d k ≤ 1)) :=
  by decide

set_option maxHeartbeats 200000 in
example  (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example  (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example  (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example  (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example  (h_mono : Monotone d) (h_no_three : ∀ k, d (k + 2) ≠ d k) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
