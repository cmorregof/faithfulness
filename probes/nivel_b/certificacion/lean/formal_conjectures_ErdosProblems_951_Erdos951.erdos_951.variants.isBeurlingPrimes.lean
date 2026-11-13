import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.NumberTheory.BeurlingPrimes
/-!
# Erdős Problem 951

*References:*
 - [erdosproblems.com/951](https://www.erdosproblems.com/951)
 - [Er77c] Erdős, Paul, Problems and results on combinatorial number theory. III. Number theory day (Proc. Conf., Rockefeller Univ.,
    New York, 1976) (1977), 43-72.
-/

section

open scoped Finsupp Nat.Prime Topology
open Filter

namespace Erdos951

/-- A sequence `a : ℕ → ℝ` is said to have property `Erdos951Prop` if for any pair of distinct
finitely supported sequences `k l : ℕ →₀ ℕ` their corresponding Beurling integers are of distance
at least one apart. -/
def Erdos951Prop (a : ℕ → ℝ) : Prop :=
  ∀ (k ℓ : ℕ →₀ ℕ), k ≠ ℓ → |beurlingInteger a k - beurlingInteger a ℓ| ≥ 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a : ℕ → ℝ} (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℝ} (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) →
    (∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℝ} (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) →
    (∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℝ} (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) →
    (∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℝ} (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) →
    (∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℝ} (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) →
    (∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℝ} (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) →
    (∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℝ} (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) →
    (∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {a : ℕ → ℝ} (hm : StrictMono a) (he : Erdos951Prop a) :
    (1 < a 0) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {a : ℕ → ℝ} (hm : StrictMono a) (he : Erdos951Prop a) :
    (1 < a 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {a : ℕ → ℝ} (hm : StrictMono a) (he : Erdos951Prop a) :
    (1 < a 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {a : ℕ → ℝ} (hm : StrictMono a) (he : Erdos951Prop a) :
    (1 < a 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {a : ℕ → ℝ} (hm : StrictMono a) (he : Erdos951Prop a) :
    (1 < a 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {a : ℕ → ℝ} (hm : StrictMono a) (he : Erdos951Prop a) :
    (1 < a 0) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {a : ℕ → ℝ} (hm : StrictMono a) (he : Erdos951Prop a) :
    (1 < a 0) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a : ℕ → ℝ} (ha : 1 ≤ a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℝ} (ha : 1 ≤ a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) →
    (∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℝ} (ha : 1 ≤ a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) →
    (∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℝ} (ha : 1 ≤ a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) →
    (∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℝ} (ha : 1 ≤ a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) →
    (∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℝ} (ha : 1 ≤ a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) →
    (∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℝ} (ha : 1 ≤ a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) →
    (∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℝ} (ha : 1 ≤ a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) →
    (∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {a : ℕ → ℝ} (hm : StrictMono a) (he : Erdos951Prop a) :
    (1 < a 0) ↔ (1 ≤ a 0) := by
  omega

set_option maxHeartbeats 200000 in
example {a : ℕ → ℝ} (hm : StrictMono a) (he : Erdos951Prop a) :
    (1 < a 0) ↔ (1 ≤ a 0) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {a : ℕ → ℝ} (hm : StrictMono a) (he : Erdos951Prop a) :
    (1 < a 0) ↔ (1 ≤ a 0) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {a : ℕ → ℝ} (hm : StrictMono a) (he : Erdos951Prop a) :
    (1 < a 0) ↔ (1 ≤ a 0) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {a : ℕ → ℝ} (hm : StrictMono a) (he : Erdos951Prop a) :
    (1 < a 0) ↔ (1 ≤ a 0) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {a : ℕ → ℝ} (hm : StrictMono a) (he : Erdos951Prop a) :
    (1 < a 0) ↔ (1 ≤ a 0) := by
  simp_all

set_option maxHeartbeats 200000 in
example {a : ℕ → ℝ} (hm : StrictMono a) (he : Erdos951Prop a) :
    (1 < a 0) ↔ (1 ≤ a 0) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a : ℕ → ℝ} (ha : a 0 > 1) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a

set_option maxHeartbeats 200000 in
example {a : ℕ → ℝ} :
    (1 < a 0) ↔ (a 0 > 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {a : ℕ → ℝ} :
    (1 < a 0) ↔ (a 0 > 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {a : ℕ → ℝ} :
    (1 < a 0) ↔ (a 0 > 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {a : ℕ → ℝ} :
    (1 < a 0) ↔ (a 0 > 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {a : ℕ → ℝ} :
    (1 < a 0) ↔ (a 0 > 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {a : ℕ → ℝ} :
    (1 < a 0) ↔ (a 0 > 1) := by
  omega

set_option maxHeartbeats 200000 in
example {a : ℕ → ℝ} :
    (1 < a 0) ↔ (a 0 > 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {a : ℕ → ℝ} :
    (1 < a 0) ↔ (a 0 > 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) ↔
    (∀ {a : ℕ → ℝ} (ha : a 0 > 1) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) ↔
    (∀ {a : ℕ → ℝ} (ha : a 0 > 1) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) ↔
    (∀ {a : ℕ → ℝ} (ha : a 0 > 1) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) ↔
    (∀ {a : ℕ → ℝ} (ha : a 0 > 1) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a : ℕ → ℝ} (hm : StrictMono a) (ha : 1 < a 0) (he : Erdos951Prop a), IsBeurlingPrimes a

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) ↔
    (∀ {a : ℕ → ℝ} (hm : StrictMono a) (ha : 1 < a 0) (he : Erdos951Prop a), IsBeurlingPrimes a) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) ↔
    (∀ {a : ℕ → ℝ} (hm : StrictMono a) (ha : 1 < a 0) (he : Erdos951Prop a), IsBeurlingPrimes a) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) ↔
    (∀ {a : ℕ → ℝ} (hm : StrictMono a) (ha : 1 < a 0) (he : Erdos951Prop a), IsBeurlingPrimes a) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) ↔
    (∀ {a : ℕ → ℝ} (hm : StrictMono a) (ha : 1 < a 0) (he : Erdos951Prop a), IsBeurlingPrimes a) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a : ℕ → ℝ} (ha₀ : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) ↔
    (∀ {a : ℕ → ℝ} (ha₀ : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) ↔
    (∀ {a : ℕ → ℝ} (ha₀ : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) ↔
    (∀ {a : ℕ → ℝ} (ha₀ : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) ↔
    (∀ {a : ℕ → ℝ} (ha₀ : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a : ℕ → ℝ} (ha : a 0 ≥ 1) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℝ} (ha : a 0 ≥ 1) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) →
    (∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℝ} (ha : a 0 ≥ 1) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) →
    (∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℝ} (ha : a 0 ≥ 1) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) →
    (∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℝ} (ha : a 0 ≥ 1) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) →
    (∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℝ} (ha : a 0 ≥ 1) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) →
    (∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℝ} (ha : a 0 ≥ 1) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) →
    (∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℝ} (ha : a 0 ≥ 1) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) →
    (∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {a : ℕ → ℝ} (hm : StrictMono a) (he : Erdos951Prop a) :
    (1 < a 0) ↔ (a 0 ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example {a : ℕ → ℝ} (hm : StrictMono a) (he : Erdos951Prop a) :
    (1 < a 0) ↔ (a 0 ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {a : ℕ → ℝ} (hm : StrictMono a) (he : Erdos951Prop a) :
    (1 < a 0) ↔ (a 0 ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {a : ℕ → ℝ} (hm : StrictMono a) (he : Erdos951Prop a) :
    (1 < a 0) ↔ (a 0 ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {a : ℕ → ℝ} (hm : StrictMono a) (he : Erdos951Prop a) :
    (1 < a 0) ↔ (a 0 ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {a : ℕ → ℝ} (hm : StrictMono a) (he : Erdos951Prop a) :
    (1 < a 0) ↔ (a 0 ≥ 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example {a : ℕ → ℝ} (hm : StrictMono a) (he : Erdos951Prop a) :
    (1 < a 0) ↔ (a 0 ≥ 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a : ℕ → ℝ} (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℝ} (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) →
    (∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℝ} (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) →
    (∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℝ} (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) →
    (∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℝ} (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) →
    (∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℝ} (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) →
    (∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℝ} (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) →
    (∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a : ℕ → ℝ} (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) →
    (∀ {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a), IsBeurlingPrimes a) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {a : ℕ → ℝ} (hm : StrictMono a) (he : Erdos951Prop a) :
    (1 < a 0) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {a : ℕ → ℝ} (hm : StrictMono a) (he : Erdos951Prop a) :
    (1 < a 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {a : ℕ → ℝ} (hm : StrictMono a) (he : Erdos951Prop a) :
    (1 < a 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {a : ℕ → ℝ} (hm : StrictMono a) (he : Erdos951Prop a) :
    (1 < a 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {a : ℕ → ℝ} (hm : StrictMono a) (he : Erdos951Prop a) :
    (1 < a 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {a : ℕ → ℝ} (hm : StrictMono a) (he : Erdos951Prop a) :
    (1 < a 0) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {a : ℕ → ℝ} (hm : StrictMono a) (he : Erdos951Prop a) :
    (1 < a 0) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {a : ℕ → ℝ} (ha : 1 < a 0) (hm : StrictMono a) (he : Erdos951Prop a) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
