import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 640

*References:*
- [erdosproblems.com/640](https://www.erdosproblems.com/640)
- [Er97d] Erdős, Paul, *Some recent problems and results in graph theory*. Discrete Math.
  (1997), 81–85, p.84.
-/

section

open SimpleGraph

namespace Erdos640

/-- An odd cycle whose vertices induce a graph of chromatic number at least `k`. -/
def HasHighChromaticOddCycle {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ v, ∃ p : G.Walk v v, p.IsCycle ∧ Odd p.length ∧
    (k : ℕ∞) ≤ (G.induce {x | x ∈ p.support}).chromaticNumber

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), HasHighChromaticOddCycle G 3

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n))  :
    ((3 : ℕ∞) ≤ G.chromaticNumber) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n))  :
    ((3 : ℕ∞) ≤ G.chromaticNumber) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n))  :
    ((3 : ℕ∞) ≤ G.chromaticNumber) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n))  :
    ((3 : ℕ∞) ≤ G.chromaticNumber) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n))  :
    ((3 : ℕ∞) ≤ G.chromaticNumber) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n))  :
    ((3 : ℕ∞) ≤ G.chromaticNumber) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n))  :
    ((3 : ℕ∞) ≤ G.chromaticNumber) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) < G.chromaticNumber), HasHighChromaticOddCycle G 3

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) < G.chromaticNumber), HasHighChromaticOddCycle G 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) < G.chromaticNumber), HasHighChromaticOddCycle G 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) < G.chromaticNumber), HasHighChromaticOddCycle G 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) < G.chromaticNumber), HasHighChromaticOddCycle G 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) < G.chromaticNumber), HasHighChromaticOddCycle G 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) < G.chromaticNumber), HasHighChromaticOddCycle G 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) < G.chromaticNumber), HasHighChromaticOddCycle G 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n))  :
    ((3 : ℕ∞) ≤ G.chromaticNumber) ↔ ((3 : ℕ∞) < G.chromaticNumber) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n))  :
    ((3 : ℕ∞) ≤ G.chromaticNumber) ↔ ((3 : ℕ∞) < G.chromaticNumber) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n))  :
    ((3 : ℕ∞) ≤ G.chromaticNumber) ↔ ((3 : ℕ∞) < G.chromaticNumber) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n))  :
    ((3 : ℕ∞) ≤ G.chromaticNumber) ↔ ((3 : ℕ∞) < G.chromaticNumber) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n))  :
    ((3 : ℕ∞) ≤ G.chromaticNumber) ↔ ((3 : ℕ∞) < G.chromaticNumber) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n))  :
    ((3 : ℕ∞) ≤ G.chromaticNumber) ↔ ((3 : ℕ∞) < G.chromaticNumber) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n))  :
    ((3 : ℕ∞) ≤ G.chromaticNumber) ↔ ((3 : ℕ∞) < G.chromaticNumber) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (4 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (4 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (4 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (4 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (4 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (4 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (4 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (4 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (4 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (4 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (4 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (4 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (4 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (4 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (4 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n))  :
    ((3 : ℕ∞) ≤ G.chromaticNumber) ↔ ((4 : ℕ∞) ≤ G.chromaticNumber) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n))  :
    ((3 : ℕ∞) ≤ G.chromaticNumber) ↔ ((4 : ℕ∞) ≤ G.chromaticNumber) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n))  :
    ((3 : ℕ∞) ≤ G.chromaticNumber) ↔ ((4 : ℕ∞) ≤ G.chromaticNumber) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n))  :
    ((3 : ℕ∞) ≤ G.chromaticNumber) ↔ ((4 : ℕ∞) ≤ G.chromaticNumber) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n))  :
    ((3 : ℕ∞) ≤ G.chromaticNumber) ↔ ((4 : ℕ∞) ≤ G.chromaticNumber) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n))  :
    ((3 : ℕ∞) ≤ G.chromaticNumber) ↔ ((4 : ℕ∞) ≤ G.chromaticNumber) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n))  :
    ((3 : ℕ∞) ≤ G.chromaticNumber) ↔ ((4 : ℕ∞) ≤ G.chromaticNumber) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.chromaticNumber ≥ (3 : ℕ∞)), HasHighChromaticOddCycle G 3

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) :
    ((3 : ℕ∞) ≤ G.chromaticNumber) ↔ (G.chromaticNumber ≥ (3 : ℕ∞)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) :
    ((3 : ℕ∞) ≤ G.chromaticNumber) ↔ (G.chromaticNumber ≥ (3 : ℕ∞)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) :
    ((3 : ℕ∞) ≤ G.chromaticNumber) ↔ (G.chromaticNumber ≥ (3 : ℕ∞)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) :
    ((3 : ℕ∞) ≤ G.chromaticNumber) ↔ (G.chromaticNumber ≥ (3 : ℕ∞)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) :
    ((3 : ℕ∞) ≤ G.chromaticNumber) ↔ (G.chromaticNumber ≥ (3 : ℕ∞)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) :
    ((3 : ℕ∞) ≤ G.chromaticNumber) ↔ (G.chromaticNumber ≥ (3 : ℕ∞)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) :
    ((3 : ℕ∞) ≤ G.chromaticNumber) ↔ (G.chromaticNumber ≥ (3 : ℕ∞)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) :
    ((3 : ℕ∞) ≤ G.chromaticNumber) ↔ (G.chromaticNumber ≥ (3 : ℕ∞)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) ↔
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.chromaticNumber ≥ (3 : ℕ∞)), HasHighChromaticOddCycle G 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) ↔
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.chromaticNumber ≥ (3 : ℕ∞)), HasHighChromaticOddCycle G 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) ↔
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.chromaticNumber ≥ (3 : ℕ∞)), HasHighChromaticOddCycle G 3) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) ↔
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.chromaticNumber ≥ (3 : ℕ∞)), HasHighChromaticOddCycle G 3) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG₀ : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) ↔
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG₀ : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) ↔
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG₀ : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) ↔
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG₀ : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) ↔
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG₀ : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.chromaticNumber > (3 : ℕ∞)), HasHighChromaticOddCycle G 3

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.chromaticNumber > (3 : ℕ∞)), HasHighChromaticOddCycle G 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.chromaticNumber > (3 : ℕ∞)), HasHighChromaticOddCycle G 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.chromaticNumber > (3 : ℕ∞)), HasHighChromaticOddCycle G 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.chromaticNumber > (3 : ℕ∞)), HasHighChromaticOddCycle G 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.chromaticNumber > (3 : ℕ∞)), HasHighChromaticOddCycle G 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.chromaticNumber > (3 : ℕ∞)), HasHighChromaticOddCycle G 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.chromaticNumber > (3 : ℕ∞)), HasHighChromaticOddCycle G 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n))  :
    ((3 : ℕ∞) ≤ G.chromaticNumber) ↔ (G.chromaticNumber > (3 : ℕ∞)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n))  :
    ((3 : ℕ∞) ≤ G.chromaticNumber) ↔ (G.chromaticNumber > (3 : ℕ∞)) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n))  :
    ((3 : ℕ∞) ≤ G.chromaticNumber) ↔ (G.chromaticNumber > (3 : ℕ∞)) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n))  :
    ((3 : ℕ∞) ≤ G.chromaticNumber) ↔ (G.chromaticNumber > (3 : ℕ∞)) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n))  :
    ((3 : ℕ∞) ≤ G.chromaticNumber) ↔ (G.chromaticNumber > (3 : ℕ∞)) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n))  :
    ((3 : ℕ∞) ≤ G.chromaticNumber) ↔ (G.chromaticNumber > (3 : ℕ∞)) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n))  :
    ((3 : ℕ∞) ≤ G.chromaticNumber) ↔ (G.chromaticNumber > (3 : ℕ∞)) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.chromaticNumber ≥ (4 : ℕ∞)), HasHighChromaticOddCycle G 3

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.chromaticNumber ≥ (4 : ℕ∞)), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.chromaticNumber ≥ (4 : ℕ∞)), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.chromaticNumber ≥ (4 : ℕ∞)), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.chromaticNumber ≥ (4 : ℕ∞)), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.chromaticNumber ≥ (4 : ℕ∞)), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.chromaticNumber ≥ (4 : ℕ∞)), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.chromaticNumber ≥ (4 : ℕ∞)), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.chromaticNumber ≥ (4 : ℕ∞)), HasHighChromaticOddCycle G 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.chromaticNumber ≥ (4 : ℕ∞)), HasHighChromaticOddCycle G 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.chromaticNumber ≥ (4 : ℕ∞)), HasHighChromaticOddCycle G 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.chromaticNumber ≥ (4 : ℕ∞)), HasHighChromaticOddCycle G 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.chromaticNumber ≥ (4 : ℕ∞)), HasHighChromaticOddCycle G 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.chromaticNumber ≥ (4 : ℕ∞)), HasHighChromaticOddCycle G 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber), HasHighChromaticOddCycle G 3) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.chromaticNumber ≥ (4 : ℕ∞)), HasHighChromaticOddCycle G 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n))  :
    ((3 : ℕ∞) ≤ G.chromaticNumber) ↔ (G.chromaticNumber ≥ (4 : ℕ∞)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n))  :
    ((3 : ℕ∞) ≤ G.chromaticNumber) ↔ (G.chromaticNumber ≥ (4 : ℕ∞)) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n))  :
    ((3 : ℕ∞) ≤ G.chromaticNumber) ↔ (G.chromaticNumber ≥ (4 : ℕ∞)) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n))  :
    ((3 : ℕ∞) ≤ G.chromaticNumber) ↔ (G.chromaticNumber ≥ (4 : ℕ∞)) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n))  :
    ((3 : ℕ∞) ≤ G.chromaticNumber) ↔ (G.chromaticNumber ≥ (4 : ℕ∞)) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n))  :
    ((3 : ℕ∞) ≤ G.chromaticNumber) ↔ (G.chromaticNumber ≥ (4 : ℕ∞)) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n))  :
    ((3 : ℕ∞) ≤ G.chromaticNumber) ↔ (G.chromaticNumber ≥ (4 : ℕ∞)) := by
  plausible

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Fin n)) (hG : (3 : ℕ∞) ≤ G.chromaticNumber) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
