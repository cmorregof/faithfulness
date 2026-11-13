import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 961

*References:*
- [erdosproblems.com/961](https://www.erdosproblems.com/961)
- [Ju74] Jutila, Matti, On numbers with a large prime factor. {II}. J. Indian Math. Soc. (N.S.) (1974), 125--130.
- [RaSh73](https://eudml.org/doc/urn:eudml:doc:205214) Ramachandra, K. and Shorey, T. N., On gaps between numbers with a large prime factor. Acta Arith. (1973), 99--111.
-/

section

open Filter Real

namespace Erdos961
noncomputable def Erdos961Prop (k n : ℕ) : Prop :=
  ∀ m ≥ k + 1, ∃ i ∈ Set.Ico m (m + n), ¬ i ∈ Nat.smoothNumbers (k + 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 0 < k), Erdos961Prop k k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k > 0), Erdos961Prop k k

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (k > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (k > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (k > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (k > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (k > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (k > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (k > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (k > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), Erdos961Prop k k) ↔
    (∀ (k : ℕ) (hk : k > 0), Erdos961Prop k k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), Erdos961Prop k k) ↔
    (∀ (k : ℕ) (hk : k > 0), Erdos961Prop k k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), Erdos961Prop k k) ↔
    (∀ (k : ℕ) (hk : k > 0), Erdos961Prop k k) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), Erdos961Prop k k) ↔
    (∀ (k : ℕ) (hk : k > 0), Erdos961Prop k k) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 0 < k), Erdos961Prop k k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk₀ : 0 < k), Erdos961Prop k k

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), Erdos961Prop k k) ↔
    (∀ (k : ℕ) (hk₀ : 0 < k), Erdos961Prop k k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), Erdos961Prop k k) ↔
    (∀ (k : ℕ) (hk₀ : 0 < k), Erdos961Prop k k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), Erdos961Prop k k) ↔
    (∀ (k : ℕ) (hk₀ : 0 < k), Erdos961Prop k k) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), Erdos961Prop k k) ↔
    (∀ (k : ℕ) (hk₀ : 0 < k), Erdos961Prop k k) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 0 < k), Erdos961Prop k k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : ¬(k ≤ 0)), Erdos961Prop k k

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (¬(k ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (¬(k ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (¬(k ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (¬(k ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (¬(k ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (¬(k ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (¬(k ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (¬(k ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), Erdos961Prop k k) ↔
    (∀ (k : ℕ) (hk : ¬(k ≤ 0)), Erdos961Prop k k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), Erdos961Prop k k) ↔
    (∀ (k : ℕ) (hk : ¬(k ≤ 0)), Erdos961Prop k k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), Erdos961Prop k k) ↔
    (∀ (k : ℕ) (hk : ¬(k ≤ 0)), Erdos961Prop k k) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), Erdos961Prop k k) ↔
    (∀ (k : ℕ) (hk : ¬(k ≤ 0)), Erdos961Prop k k) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 0 < k), Erdos961Prop k k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), Erdos961Prop k k

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (1 ≤ k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (1 ≤ k) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (1 ≤ k) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (1 ≤ k) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (1 ≤ k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (1 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (1 ≤ k) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (0 < k) ↔ (1 ≤ k) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), Erdos961Prop k k) ↔
    (∀ (k : ℕ) (hk : 1 ≤ k), Erdos961Prop k k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), Erdos961Prop k k) ↔
    (∀ (k : ℕ) (hk : 1 ≤ k), Erdos961Prop k k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), Erdos961Prop k k) ↔
    (∀ (k : ℕ) (hk : 1 ≤ k), Erdos961Prop k k) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), Erdos961Prop k k) ↔
    (∀ (k : ℕ) (hk : 1 ≤ k), Erdos961Prop k k) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 0 < k), Erdos961Prop k k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 < k), Erdos961Prop k k

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), Erdos961Prop k k) →
    (∀ (k : ℕ) (hk : 1 < k), Erdos961Prop k k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), Erdos961Prop k k) →
    (∀ (k : ℕ) (hk : 1 < k), Erdos961Prop k k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), Erdos961Prop k k) →
    (∀ (k : ℕ) (hk : 1 < k), Erdos961Prop k k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), Erdos961Prop k k) →
    (∀ (k : ℕ) (hk : 1 < k), Erdos961Prop k k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), Erdos961Prop k k) →
    (∀ (k : ℕ) (hk : 1 < k), Erdos961Prop k k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), Erdos961Prop k k) →
    (∀ (k : ℕ) (hk : 1 < k), Erdos961Prop k k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k), Erdos961Prop k k) →
    (∀ (k : ℕ) (hk : 1 < k), Erdos961Prop k k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (0 < k) ↔ (1 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (0 < k) ↔ (1 < k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (0 < k) ↔ (1 < k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (0 < k) ↔ (1 < k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (0 < k) ↔ (1 < k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (0 < k) ↔ (1 < k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (0 < k) ↔ (1 < k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((0 < k) ↔ (1 < k))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((0 < k) ↔ (1 < k))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((0 < k) ↔ (1 < k))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((0 < k) ↔ (1 < k))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((0 < k) ↔ (1 < k))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((0 < k) ↔ (1 < k))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (1 < k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (1 < k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (1 < k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (1 < k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (1 < k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (1 < k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 0 < k) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 0 < k) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 0 < k) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 0 < k) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 0 < k) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
