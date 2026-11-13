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
  ∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r < d (k + 2 * r) - d k

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r < d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r < d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r < d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r < d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r < d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r < d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r < d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (Monotone d) ∧ (∀ i, d (i + 2) ≠ d i) ∧ (¬(r < d (k + 2 * r) - d k)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (Monotone d) ∧ (∀ i, d (i + 2) ≠ d i) ∧ (¬(r < d (k + 2 * r) - d k)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((r ≤ d (k + 2 * r) - d k) ↔ (r < d (k + 2 * r) - d k)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((r ≤ d (k + 2 * r) - d k) ↔ (r < d (k + 2 * r) - d k)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 3) ≠ d i), r ≤ d (k + 2 * r) - d k

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 3) ≠ d i), r ≤ d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 3) ≠ d i), r ≤ d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 3) ≠ d i), r ≤ d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 3) ≠ d i), r ≤ d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 3) ≠ d i), r ≤ d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 3) ≠ d i), r ≤ d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 3) ≠ d i), r ≤ d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 3) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 3) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 3) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 3) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 3) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 3) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 3) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example  (h_mono : Monotone d) :
    (∀ i, d (i + 2) ≠ d i) ↔ (∀ i, d (i + 3) ≠ d i) := by
  omega

set_option maxHeartbeats 200000 in
example  (h_mono : Monotone d) :
    (∀ i, d (i + 2) ≠ d i) ↔ (∀ i, d (i + 3) ≠ d i) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example  (h_mono : Monotone d) :
    (∀ i, d (i + 2) ≠ d i) ↔ (∀ i, d (i + 3) ≠ d i) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example  (h_mono : Monotone d) :
    (∀ i, d (i + 2) ≠ d i) ↔ (∀ i, d (i + 3) ≠ d i) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example  (h_mono : Monotone d) :
    (∀ i, d (i + 2) ≠ d i) ↔ (∀ i, d (i + 3) ≠ d i) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example  (h_mono : Monotone d) :
    (∀ i, d (i + 2) ≠ d i) ↔ (∀ i, d (i + 3) ≠ d i) := by
  simp_all

set_option maxHeartbeats 200000 in
example  (h_mono : Monotone d) :
    (∀ i, d (i + 2) ≠ d i) ↔ (∀ i, d (i + 3) ≠ d i) := by
  plausible

set_option maxHeartbeats 200000 in
example : (Monotone d) ∧ (¬((∀ i, d (i + 2) ≠ d i) ↔ (∀ i, d (i + 3) ≠ d i))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (Monotone d) ∧ (¬((∀ i, d (i + 2) ≠ d i) ↔ (∀ i, d (i + 3) ≠ d i))) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((∀ i, d (i + 2) ≠ d i) ↔ (∀ i, d (i + 3) ≠ d i)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((∀ i, d (i + 2) ≠ d i) ↔ (∀ i, d (i + 3) ≠ d i)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≥ d (k + 2 * r) - d k

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≥ d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≥ d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≥ d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≥ d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≥ d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≥ d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≥ d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≥ d (k + 2 * r) - d k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≥ d (k + 2 * r) - d k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≥ d (k + 2 * r) - d k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≥ d (k + 2 * r) - d k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≥ d (k + 2 * r) - d k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≥ d (k + 2 * r) - d k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≥ d (k + 2 * r) - d k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (Monotone d) ∧ (∀ i, d (i + 2) ≠ d i) ∧ (¬(r ≥ d (k + 2 * r) - d k)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (Monotone d) ∧ (∀ i, d (i + 2) ≠ d i) ∧ (¬(r ≥ d (k + 2 * r) - d k)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((r ≤ d (k + 2 * r) - d k) ↔ (r ≥ d (k + 2 * r) - d k)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((r ≤ d (k + 2 * r) - d k) ↔ (r ≥ d (k + 2 * r) - d k)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), d (k + 2 * r) - d k ≥ r

set_option maxHeartbeats 200000 in
example  :
    (r ≤ d (k + 2 * r) - d k) ↔ (d (k + 2 * r) - d k ≥ r) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example  :
    (r ≤ d (k + 2 * r) - d k) ↔ (d (k + 2 * r) - d k ≥ r) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example  :
    (r ≤ d (k + 2 * r) - d k) ↔ (d (k + 2 * r) - d k ≥ r) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example  :
    (r ≤ d (k + 2 * r) - d k) ↔ (d (k + 2 * r) - d k ≥ r) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example  :
    (r ≤ d (k + 2 * r) - d k) ↔ (d (k + 2 * r) - d k ≥ r) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example  :
    (r ≤ d (k + 2 * r) - d k) ↔ (d (k + 2 * r) - d k ≥ r) := by
  omega

set_option maxHeartbeats 200000 in
example  :
    (r ≤ d (k + 2 * r) - d k) ↔ (d (k + 2 * r) - d k ≥ r) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example  :
    (r ≤ d (k + 2 * r) - d k) ↔ (d (k + 2 * r) - d k ≥ r) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) ↔
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), d (k + 2 * r) - d k ≥ r) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) ↔
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), d (k + 2 * r) - d k ≥ r) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) ↔
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), d (k + 2 * r) - d k ≥ r) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) ↔
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), d (k + 2 * r) - d k ≥ r) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h_no_three : ∀ i, d (i + 2) ≠ d i) (h_mono : Monotone d), r ≤ d (k + 2 * r) - d k

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) ↔
    (∀ (h_no_three : ∀ i, d (i + 2) ≠ d i) (h_mono : Monotone d), r ≤ d (k + 2 * r) - d k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) ↔
    (∀ (h_no_three : ∀ i, d (i + 2) ≠ d i) (h_mono : Monotone d), r ≤ d (k + 2 * r) - d k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) ↔
    (∀ (h_no_three : ∀ i, d (i + 2) ≠ d i) (h_mono : Monotone d), r ≤ d (k + 2 * r) - d k) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) ↔
    (∀ (h_no_three : ∀ i, d (i + 2) ≠ d i) (h_mono : Monotone d), r ≤ d (k + 2 * r) - d k) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h_mono₀ : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) ↔
    (∀ (h_mono₀ : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) ↔
    (∀ (h_mono₀ : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) ↔
    (∀ (h_mono₀ : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) ↔
    (∀ (h_mono₀ : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), ¬(d (k + 2 * r) - d k < r)

set_option maxHeartbeats 200000 in
example  :
    (r ≤ d (k + 2 * r) - d k) ↔ (¬(d (k + 2 * r) - d k < r)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example  :
    (r ≤ d (k + 2 * r) - d k) ↔ (¬(d (k + 2 * r) - d k < r)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example  :
    (r ≤ d (k + 2 * r) - d k) ↔ (¬(d (k + 2 * r) - d k < r)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example  :
    (r ≤ d (k + 2 * r) - d k) ↔ (¬(d (k + 2 * r) - d k < r)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example  :
    (r ≤ d (k + 2 * r) - d k) ↔ (¬(d (k + 2 * r) - d k < r)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example  :
    (r ≤ d (k + 2 * r) - d k) ↔ (¬(d (k + 2 * r) - d k < r)) := by
  omega

set_option maxHeartbeats 200000 in
example  :
    (r ≤ d (k + 2 * r) - d k) ↔ (¬(d (k + 2 * r) - d k < r)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example  :
    (r ≤ d (k + 2 * r) - d k) ↔ (¬(d (k + 2 * r) - d k < r)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) ↔
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), ¬(d (k + 2 * r) - d k < r)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) ↔
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), ¬(d (k + 2 * r) - d k < r)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) ↔
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), ¬(d (k + 2 * r) - d k < r)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) ↔
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), ¬(d (k + 2 * r) - d k < r)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), d (k + 2 * r) - d k > r

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), d (k + 2 * r) - d k > r) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), d (k + 2 * r) - d k > r) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), d (k + 2 * r) - d k > r) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), d (k + 2 * r) - d k > r) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), d (k + 2 * r) - d k > r) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), d (k + 2 * r) - d k > r) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), d (k + 2 * r) - d k > r) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (Monotone d) ∧ (∀ i, d (i + 2) ≠ d i) ∧ (¬(d (k + 2 * r) - d k > r)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (Monotone d) ∧ (∀ i, d (i + 2) ≠ d i) ∧ (¬(d (k + 2 * r) - d k > r)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((r ≤ d (k + 2 * r) - d k) ↔ (d (k + 2 * r) - d k > r)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((r ≤ d (k + 2 * r) - d k) ↔ (d (k + 2 * r) - d k > r)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 3) ≠ d i), d (k + 2 * r) - d k ≥ r

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 3) ≠ d i), d (k + 2 * r) - d k ≥ r) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 3) ≠ d i), d (k + 2 * r) - d k ≥ r) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 3) ≠ d i), d (k + 2 * r) - d k ≥ r) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 3) ≠ d i), d (k + 2 * r) - d k ≥ r) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 3) ≠ d i), d (k + 2 * r) - d k ≥ r) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 3) ≠ d i), d (k + 2 * r) - d k ≥ r) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 3) ≠ d i), d (k + 2 * r) - d k ≥ r) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 3) ≠ d i), d (k + 2 * r) - d k ≥ r) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 3) ≠ d i), d (k + 2 * r) - d k ≥ r) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 3) ≠ d i), d (k + 2 * r) - d k ≥ r) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 3) ≠ d i), d (k + 2 * r) - d k ≥ r) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 3) ≠ d i), d (k + 2 * r) - d k ≥ r) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 3) ≠ d i), d (k + 2 * r) - d k ≥ r) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 3) ≠ d i), d (k + 2 * r) - d k ≥ r) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example  (h_mono : Monotone d) :
    (∀ i, d (i + 2) ≠ d i) ↔ (∀ i, d (i + 3) ≠ d i) := by
  omega

set_option maxHeartbeats 200000 in
example  (h_mono : Monotone d) :
    (∀ i, d (i + 2) ≠ d i) ↔ (∀ i, d (i + 3) ≠ d i) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example  (h_mono : Monotone d) :
    (∀ i, d (i + 2) ≠ d i) ↔ (∀ i, d (i + 3) ≠ d i) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example  (h_mono : Monotone d) :
    (∀ i, d (i + 2) ≠ d i) ↔ (∀ i, d (i + 3) ≠ d i) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example  (h_mono : Monotone d) :
    (∀ i, d (i + 2) ≠ d i) ↔ (∀ i, d (i + 3) ≠ d i) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example  (h_mono : Monotone d) :
    (∀ i, d (i + 2) ≠ d i) ↔ (∀ i, d (i + 3) ≠ d i) := by
  simp_all

set_option maxHeartbeats 200000 in
example  (h_mono : Monotone d) :
    (∀ i, d (i + 2) ≠ d i) ↔ (∀ i, d (i + 3) ≠ d i) := by
  plausible

set_option maxHeartbeats 200000 in
example : (Monotone d) ∧ (¬((∀ i, d (i + 2) ≠ d i) ↔ (∀ i, d (i + 3) ≠ d i))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (Monotone d) ∧ (¬((∀ i, d (i + 2) ≠ d i) ↔ (∀ i, d (i + 3) ≠ d i))) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((∀ i, d (i + 2) ≠ d i) ↔ (∀ i, d (i + 3) ≠ d i)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((∀ i, d (i + 2) ≠ d i) ↔ (∀ i, d (i + 3) ≠ d i)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), d (k + 2 * r) - d k ≤ r

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), d (k + 2 * r) - d k ≤ r) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), d (k + 2 * r) - d k ≤ r) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), d (k + 2 * r) - d k ≤ r) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), d (k + 2 * r) - d k ≤ r) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), d (k + 2 * r) - d k ≤ r) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), d (k + 2 * r) - d k ≤ r) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), d (k + 2 * r) - d k ≤ r) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), d (k + 2 * r) - d k ≤ r) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), d (k + 2 * r) - d k ≤ r) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), d (k + 2 * r) - d k ≤ r) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), d (k + 2 * r) - d k ≤ r) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), d (k + 2 * r) - d k ≤ r) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), d (k + 2 * r) - d k ≤ r) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), r ≤ d (k + 2 * r) - d k) →
    (∀ (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i), d (k + 2 * r) - d k ≤ r) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (Monotone d) ∧ (∀ i, d (i + 2) ≠ d i) ∧ (¬(d (k + 2 * r) - d k ≤ r)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (Monotone d) ∧ (∀ i, d (i + 2) ≠ d i) ∧ (¬(d (k + 2 * r) - d k ≤ r)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((r ≤ d (k + 2 * r) - d k) ↔ (d (k + 2 * r) - d k ≤ r)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((r ≤ d (k + 2 * r) - d k) ↔ (d (k + 2 * r) - d k ≤ r)) :=
  by decide

set_option maxHeartbeats 200000 in
example  (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example  (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example  (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example  (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example  (h_mono : Monotone d) (h_no_three : ∀ i, d (i + 2) ≠ d i) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
