import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 1079

*References:*
- [erdosproblems.com/1079](https://www.erdosproblems.com/1079)
- [Er75] Erdős, P., *Some recent progress on extremal problems in graph theory*. Congr. Numer.
  (1975), 3-14.
- [BoTh81] Bollobás, Béla and Thomason, Andrew, *Dense neighbourhoods and Turán's theorem*. J.
  Combin. Theory Ser. B (1981), 111--114.
- [Bo83b] Bondy, J. A., *Large dense neighbourhoods and Turán's theorem*. J. Combin. Theory Ser.
  B (1983), 109--111.
-/

section

open SimpleGraph

namespace Erdos1079

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) :
    (4 ≤ r) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) :
    (4 ≤ r) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) :
    (4 ≤ r) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) :
    (4 ≤ r) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) :
    (4 ≤ r) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) :
    (4 ≤ r) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) :
    (4 ≤ r) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((4 ≤ r) ↔ (True)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((4 ≤ r) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((4 ≤ r) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((4 ≤ r) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((4 ≤ r) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((4 ≤ r) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((4 ≤ r) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) ≤ G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) ≤ G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) ≤ G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) ≤ G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) ≤ G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) ≤ G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) ≤ G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) ≤ G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hr : 4 ≤ r) :
    (extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) ↔ (extremalNumber n (completeGraph (Fin r)) ≤ G.edgeSet.ncard) := by
  omega

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hr : 4 ≤ r) :
    (extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) ↔ (extremalNumber n (completeGraph (Fin r)) ≤ G.edgeSet.ncard) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hr : 4 ≤ r) :
    (extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) ↔ (extremalNumber n (completeGraph (Fin r)) ≤ G.edgeSet.ncard) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hr : 4 ≤ r) :
    (extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) ↔ (extremalNumber n (completeGraph (Fin r)) ≤ G.edgeSet.ncard) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hr : 4 ≤ r) :
    (extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) ↔ (extremalNumber n (completeGraph (Fin r)) ≤ G.edgeSet.ncard) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hr : 4 ≤ r) :
    (extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) ↔ (extremalNumber n (completeGraph (Fin r)) ≤ G.edgeSet.ncard) := by
  simp_all

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hr : 4 ≤ r) :
    (extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) ↔ (extremalNumber n (completeGraph (Fin r)) ≤ G.edgeSet.ncard) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r n : ℕ) (hr : 4 < r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 < r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 < r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 < r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 < r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 < r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 < r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 < r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) :
    (4 ≤ r) ↔ (4 < r) := by
  omega

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) :
    (4 ≤ r) ↔ (4 < r) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) :
    (4 ≤ r) ↔ (4 < r) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) :
    (4 ≤ r) ↔ (4 < r) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) :
    (4 ≤ r) ↔ (4 < r) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) :
    (4 ≤ r) ↔ (4 < r) := by
  simp_all

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) :
    (4 ≤ r) ↔ (4 < r) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((4 ≤ r) ↔ (4 < r)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((4 ≤ r) ↔ (4 < r)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((4 ≤ r) ↔ (4 < r)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((4 ≤ r) ↔ (4 < r)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((4 ≤ r) ↔ (4 < r)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((4 ≤ r) ↔ (4 < r)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((4 ≤ r) ↔ (4 < r)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 3 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 3 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 3 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 3 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 3 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 3 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 3 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 3 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 3 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 3 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 3 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 3 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 3 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 3 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 3 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r n : ℕ) (hr : r ≥ 4) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (4 ≤ r) ↔ (r ≥ 4) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (4 ≤ r) ↔ (r ≥ 4) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (4 ≤ r) ↔ (r ≥ 4) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (4 ≤ r) ↔ (r ≥ 4) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (4 ≤ r) ↔ (r ≥ 4) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (4 ≤ r) ↔ (r ≥ 4) := by
  omega

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (4 ≤ r) ↔ (r ≥ 4) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (4 ≤ r) ↔ (r ≥ 4) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) ↔
    (∀ (r n : ℕ) (hr : r ≥ 4) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) ↔
    (∀ (r n : ℕ) (hr : r ≥ 4) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) ↔
    (∀ (r n : ℕ) (hr : r ≥ 4) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) ↔
    (∀ (r n : ℕ) (hr : r ≥ 4) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v₁ : Fin n, G.degree v₁ = G.maxDegree ∧ n ≤ 2 * G.degree v₁ ∧
      extremalNumber (G.degree v₁) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v₁ x}.ncard

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) ↔ (∃ v₁ : Fin n, G.degree v₁ = G.maxDegree ∧ n ≤ 2 * G.degree v₁ ∧
      extremalNumber (G.degree v₁) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v₁ x}.ncard) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) ↔ (∃ v₁ : Fin n, G.degree v₁ = G.maxDegree ∧ n ≤ 2 * G.degree v₁ ∧
      extremalNumber (G.degree v₁) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v₁ x}.ncard) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) ↔ (∃ v₁ : Fin n, G.degree v₁ = G.maxDegree ∧ n ≤ 2 * G.degree v₁ ∧
      extremalNumber (G.degree v₁) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v₁ x}.ncard) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) ↔ (∃ v₁ : Fin n, G.degree v₁ = G.maxDegree ∧ n ≤ 2 * G.degree v₁ ∧
      extremalNumber (G.degree v₁) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v₁ x}.ncard) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) ↔ (∃ v₁ : Fin n, G.degree v₁ = G.maxDegree ∧ n ≤ 2 * G.degree v₁ ∧
      extremalNumber (G.degree v₁) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v₁ x}.ncard) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) ↔ (∃ v₁ : Fin n, G.degree v₁ = G.maxDegree ∧ n ≤ 2 * G.degree v₁ ∧
      extremalNumber (G.degree v₁) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v₁ x}.ncard) := by
  omega

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) ↔ (∃ v₁ : Fin n, G.degree v₁ = G.maxDegree ∧ n ≤ 2 * G.degree v₁ ∧
      extremalNumber (G.degree v₁) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v₁ x}.ncard) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) ↔ (∃ v₁ : Fin n, G.degree v₁ = G.maxDegree ∧ n ≤ 2 * G.degree v₁ ∧
      extremalNumber (G.degree v₁) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v₁ x}.ncard) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) ↔
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v₁ : Fin n, G.degree v₁ = G.maxDegree ∧ n ≤ 2 * G.degree v₁ ∧
      extremalNumber (G.degree v₁) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v₁ x}.ncard) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) ↔
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v₁ : Fin n, G.degree v₁ = G.maxDegree ∧ n ≤ 2 * G.degree v₁ ∧
      extremalNumber (G.degree v₁) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v₁ x}.ncard) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) ↔
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v₁ : Fin n, G.degree v₁ = G.maxDegree ∧ n ≤ 2 * G.degree v₁ ∧
      extremalNumber (G.degree v₁) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v₁ x}.ncard) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) ↔
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v₁ : Fin n, G.degree v₁ = G.maxDegree ∧ n ≤ 2 * G.degree v₁ ∧
      extremalNumber (G.degree v₁) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v₁ x}.ncard) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r n : ℕ) (hr₀ : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) ↔
    (∀ (r n : ℕ) (hr₀ : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) ↔
    (∀ (r n : ℕ) (hr₀ : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) ↔
    (∀ (r n : ℕ) (hr₀ : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) ↔
    (∀ (r n : ℕ) (hr₀ : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r n : ℕ) (hr : ¬(r < 4)) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (4 ≤ r) ↔ (¬(r < 4)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (4 ≤ r) ↔ (¬(r < 4)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (4 ≤ r) ↔ (¬(r < 4)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (4 ≤ r) ↔ (¬(r < 4)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (4 ≤ r) ↔ (¬(r < 4)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (4 ≤ r) ↔ (¬(r < 4)) := by
  omega

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (4 ≤ r) ↔ (¬(r < 4)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (4 ≤ r) ↔ (¬(r < 4)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) ↔
    (∀ (r n : ℕ) (hr : ¬(r < 4)) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) ↔
    (∀ (r n : ℕ) (hr : ¬(r < 4)) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) ↔
    (∀ (r n : ℕ) (hr : ¬(r < 4)) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) ↔
    (∀ (r n : ℕ) (hr : ¬(r < 4)) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r n : ℕ) (hr : 3 < r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (4 ≤ r) ↔ (3 < r) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (4 ≤ r) ↔ (3 < r) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (4 ≤ r) ↔ (3 < r) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (4 ≤ r) ↔ (3 < r) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (4 ≤ r) ↔ (3 < r) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (4 ≤ r) ↔ (3 < r) := by
  omega

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (4 ≤ r) ↔ (3 < r) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (4 ≤ r) ↔ (3 < r) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) ↔
    (∀ (r n : ℕ) (hr : 3 < r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) ↔
    (∀ (r n : ℕ) (hr : 3 < r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) ↔
    (∀ (r n : ℕ) (hr : 3 < r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) ↔
    (∀ (r n : ℕ) (hr : 3 < r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r n : ℕ) (hr : r ≥ 4) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) ≤ G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : r ≥ 4) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) ≤ G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : r ≥ 4) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) ≤ G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : r ≥ 4) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) ≤ G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : r ≥ 4) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) ≤ G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : r ≥ 4) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) ≤ G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : r ≥ 4) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) ≤ G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : r ≥ 4) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) ≤ G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hr : 4 ≤ r) :
    (extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) ↔ (extremalNumber n (completeGraph (Fin r)) ≤ G.edgeSet.ncard) := by
  omega

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hr : 4 ≤ r) :
    (extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) ↔ (extremalNumber n (completeGraph (Fin r)) ≤ G.edgeSet.ncard) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hr : 4 ≤ r) :
    (extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) ↔ (extremalNumber n (completeGraph (Fin r)) ≤ G.edgeSet.ncard) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hr : 4 ≤ r) :
    (extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) ↔ (extremalNumber n (completeGraph (Fin r)) ≤ G.edgeSet.ncard) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hr : 4 ≤ r) :
    (extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) ↔ (extremalNumber n (completeGraph (Fin r)) ≤ G.edgeSet.ncard) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hr : 4 ≤ r) :
    (extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) ↔ (extremalNumber n (completeGraph (Fin r)) ≤ G.edgeSet.ncard) := by
  simp_all

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hr : 4 ≤ r) :
    (extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) ↔ (extremalNumber n (completeGraph (Fin r)) ≤ G.edgeSet.ncard) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r n : ℕ) (hr : r > 4) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : r > 4) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : r > 4) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : r > 4) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : r > 4) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : r > 4) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : r > 4) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : r > 4) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) :
    (4 ≤ r) ↔ (r > 4) := by
  omega

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) :
    (4 ≤ r) ↔ (r > 4) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) :
    (4 ≤ r) ↔ (r > 4) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) :
    (4 ≤ r) ↔ (r > 4) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) :
    (4 ≤ r) ↔ (r > 4) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) :
    (4 ≤ r) ↔ (r > 4) := by
  simp_all

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) :
    (4 ≤ r) ↔ (r > 4) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((4 ≤ r) ↔ (r > 4)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((4 ≤ r) ↔ (r > 4)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((4 ≤ r) ↔ (r > 4)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((4 ≤ r) ↔ (r > 4)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((4 ≤ r) ↔ (r > 4)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((4 ≤ r) ↔ (r > 4)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((4 ≤ r) ↔ (r > 4)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r n : ℕ) (hr : r ≥ 4) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 3 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : r ≥ 4) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 3 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : r ≥ 4) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 3 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : r ≥ 4) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 3 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : r ≥ 4) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 3 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : r ≥ 4) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 3 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : r ≥ 4) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 3 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : r ≥ 4) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 3 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : r ≥ 4) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 3 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : r ≥ 4) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 3 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : r ≥ 4) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 3 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : r ≥ 4) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 3 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : r ≥ 4) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 3 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : r ≥ 4) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 3 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : r ≥ 4) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 3 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r n : ℕ) (hr : 3 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 3 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 3 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 3 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 3 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 3 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 3 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 3 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) :
    (4 ≤ r) ↔ (3 ≤ r) := by
  omega

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) :
    (4 ≤ r) ↔ (3 ≤ r) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) :
    (4 ≤ r) ↔ (3 ≤ r) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) :
    (4 ≤ r) ↔ (3 ≤ r) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) :
    (4 ≤ r) ↔ (3 ≤ r) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) :
    (4 ≤ r) ↔ (3 ≤ r) := by
  simp_all

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) :
    (4 ≤ r) ↔ (3 ≤ r) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((4 ≤ r) ↔ (3 ≤ r)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((4 ≤ r) ↔ (3 ≤ r)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((4 ≤ r) ↔ (3 ≤ r)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((4 ≤ r) ↔ (3 ≤ r)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((4 ≤ r) ↔ (3 ≤ r)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((4 ≤ r) ↔ (3 ≤ r)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((4 ≤ r) ↔ (3 ≤ r)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r n : ℕ) (hr : 3 < r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 3 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 3 < r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 3 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 3 < r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 3 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 3 < r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 3 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 3 < r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 3 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 3 < r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 3 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 3 < r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 3 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 3 < r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 3 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 3 < r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 3 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 3 < r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 3 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 3 < r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 3 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 3 < r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 3 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 3 < r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 3 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 3 < r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 3 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r n : ℕ) (hr : 4 ≤ r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) →
    (∀ (r n : ℕ) (hr : 3 < r) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard), ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 3 * G.degree v ∧
      extremalNumber (G.degree v) (completeGraph (Fin (r - 1))) <
        {e ∈ G.edgeSet | ∀ x ∈ e, G.Adj v x}.ncard) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hr : 4 ≤ r) (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hr : 4 ≤ r) (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hr : 4 ≤ r) (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hr : 4 ≤ r) (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (r n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hr : 4 ≤ r) (hG : extremalNumber n (completeGraph (Fin r)) < G.edgeSet.ncard) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
