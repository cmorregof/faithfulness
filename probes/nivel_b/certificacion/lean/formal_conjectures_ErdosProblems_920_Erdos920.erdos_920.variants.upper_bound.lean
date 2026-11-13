import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   notación asintótica `≪` (FCM.Analysis.Asymptotics.Basic)
/-!
# Erdős Problem 920

*References:*
- [erdosproblems.com/166](https://www.erdosproblems.com/166)
- [erdosproblems.com/920](https://www.erdosproblems.com/920)
- [erdosproblems.com/986](https://www.erdosproblems.com/986)
- [erdosproblems.com/1104](https://www.erdosproblems.com/1104)
- [Br26] D. Brada\v{c}, Nearly tight exponents for off-diagonal Ramsey numbers. arXiv:2605.28793
  (2026).
- [Er69b] Erdős, P., Problems and results in chromatic graph theory. Proof Techniques in Graph
  Theory (Proc. Second Ann Arbor Graph Theory Conf., Ann Arbor, Mich., 1968) (1969), 27-35.
- [GrYa68] Graver, Jack E. and Yackel, James, Some graph theoretic results associated with Ramsey's
  theorem. J. Combinatorial Theory (1968), 125--175.
- [MaVe23] Mattheus, S. and Verstraete, J., The asymptotics of $r(4,t)$. arXiv:2306.04007 (2023).
-/

section

open Real Filter

namespace Erdos920

/--
$f_k(n)$ is the maximum possible chromatic number of a graph with $n$ vertices
which contains no $K_k$.
-/
noncomputable def f (k n : ℕ) : ℕ :=
  sSup {(G.chromaticNumber) | (G : SimpleGraph (Fin n)) (_ : G.CliqueFree k)}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k > 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) →
    (∀ (k : ℕ) (hk : k > 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) →
    (∀ (k : ℕ) (hk : k > 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) →
    (∀ (k : ℕ) (hk : k > 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) →
    (∀ (k : ℕ) (hk : k > 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) →
    (∀ (k : ℕ) (hk : k > 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) →
    (∀ (k : ℕ) (hk : k > 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) →
    (∀ (k : ℕ) (hk : k > 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k ≥ 3) ↔ (k > 3) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k ≥ 3) ↔ (k > 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k ≥ 3) ↔ (k > 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k ≥ 3) ↔ (k > 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k ≥ 3) ↔ (k > 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k ≥ 3) ↔ (k > 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k ≥ 3) ↔ (k > 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 3) ↔ (k > 3))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 3) ↔ (k > 3))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 3) ↔ (k > 3))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 3) ↔ (k > 3))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 3) ↔ (k > 3))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 3) ↔ (k > 3))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 3) ↔ (k > 3))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 3) ↔ (k > 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 3) ↔ (k > 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 3) ↔ (k > 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 3) ↔ (k > 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 3) ↔ (k > 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 3) ↔ (k > 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 3) ↔ (k > 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k ≥ 3) ↔ (3 ≤ k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k ≥ 3) ↔ (3 ≤ k) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k ≥ 3) ↔ (3 ≤ k) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k ≥ 3) ↔ (3 ≤ k) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k ≥ 3) ↔ (3 ≤ k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k ≥ 3) ↔ (3 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k ≥ 3) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k ≥ 3) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) ↔
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) ↔
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) ↔
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) ↔
    (∀ (k : ℕ) (hk : 3 ≤ k), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk₀ : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) ↔
    (∀ (k : ℕ) (hk₀ : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) ↔
    (∀ (k : ℕ) (hk₀ : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) ↔
    (∀ (k : ℕ) (hk₀ : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) ↔
    (∀ (k : ℕ) (hk₀ : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : ¬(k < 3)), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k ≥ 3) ↔ (¬(k < 3)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k ≥ 3) ↔ (¬(k < 3)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k ≥ 3) ↔ (¬(k < 3)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k ≥ 3) ↔ (¬(k < 3)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k ≥ 3) ↔ (¬(k < 3)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k ≥ 3) ↔ (¬(k < 3)) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k ≥ 3) ↔ (¬(k < 3)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k ≥ 3) ↔ (¬(k < 3)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) ↔
    (∀ (k : ℕ) (hk : ¬(k < 3)), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) ↔
    (∀ (k : ℕ) (hk : ¬(k < 3)), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) ↔
    (∀ (k : ℕ) (hk : ¬(k < 3)), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) ↔
    (∀ (k : ℕ) (hk : ¬(k < 3)), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k > 2), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k ≥ 3) ↔ (k > 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k ≥ 3) ↔ (k > 2) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k ≥ 3) ↔ (k > 2) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k ≥ 3) ↔ (k > 2) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k ≥ 3) ↔ (k > 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k ≥ 3) ↔ (k > 2) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k ≥ 3) ↔ (k > 2) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k ≥ 3) ↔ (k > 2) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) ↔
    (∀ (k : ℕ) (hk : k > 2), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) ↔
    (∀ (k : ℕ) (hk : k > 2), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) ↔
    (∀ (k : ℕ) (hk : k > 2), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) ↔
    (∀ (k : ℕ) (hk : k > 2), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 < k), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) →
    (∀ (k : ℕ) (hk : 3 < k), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) →
    (∀ (k : ℕ) (hk : 3 < k), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) →
    (∀ (k : ℕ) (hk : 3 < k), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) →
    (∀ (k : ℕ) (hk : 3 < k), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) →
    (∀ (k : ℕ) (hk : 3 < k), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) →
    (∀ (k : ℕ) (hk : 3 < k), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) →
    (∀ (k : ℕ) (hk : 3 < k), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k ≥ 3) ↔ (3 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k ≥ 3) ↔ (3 < k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k ≥ 3) ↔ (3 < k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k ≥ 3) ↔ (3 < k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k ≥ 3) ↔ (3 < k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k ≥ 3) ↔ (3 < k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k ≥ 3) ↔ (3 < k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 3) ↔ (3 < k))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 3) ↔ (3 < k))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 3) ↔ (3 < k))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 3) ↔ (3 < k))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 3) ↔ (3 < k))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 3) ↔ (3 < k))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 3) ↔ (3 < k))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 3) ↔ (3 < k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 3) ↔ (3 < k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 3) ↔ (3 < k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 3) ↔ (3 < k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 3) ↔ (3 < k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 3) ↔ (3 < k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 3) ↔ (3 < k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 2), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) →
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) →
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) →
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) →
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) →
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) →
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 2), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) →
    (∀ (k : ℕ) (hk : k ≥ 3), (fun n ↦ f k n) ≪ (fun n ↦ ((n : ℝ) * log (log n) / log n) ^ (1 - 1 / ((k : ℝ) - 1)))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k ≥ 3) ↔ (k ≥ 2) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k ≥ 3) ↔ (k ≥ 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k ≥ 3) ↔ (k ≥ 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k ≥ 3) ↔ (k ≥ 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k ≥ 3) ↔ (k ≥ 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k ≥ 3) ↔ (k ≥ 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k ≥ 3) ↔ (k ≥ 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 3) ↔ (k ≥ 2))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 3) ↔ (k ≥ 2))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 3) ↔ (k ≥ 2))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 3) ↔ (k ≥ 2))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 3) ↔ (k ≥ 2))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 3) ↔ (k ≥ 2))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k ≥ 3) ↔ (k ≥ 2))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 3) ↔ (k ≥ 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 3) ↔ (k ≥ 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 3) ↔ (k ≥ 2)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 3) ↔ (k ≥ 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 3) ↔ (k ≥ 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 3) ↔ (k ≥ 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≥ 3) ↔ (k ≥ 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : k ≥ 3) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : k ≥ 3) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : k ≥ 3) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : k ≥ 3) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : k ≥ 3) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
