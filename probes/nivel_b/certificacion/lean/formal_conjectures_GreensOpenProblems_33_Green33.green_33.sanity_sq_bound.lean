import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Ben Green's Open Problem 33

*References:*
- [Gr24] [Ben Green's Open Problem 33](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.33)
- [CaHa20] Caprace, Pierre-Emmanuel, and Pierre de la Harpe. "Groups with irreducibly unfaithful
  subsets for unitary representations." Confluentes Mathematici 12.1 (2020): 31-68.
- [CrLe07] Croot, Ernie, and Vsevolod F. Lev. "Open problems in additive combinatorics."
  Additive combinatorics 43.207-233 (2007): 1.
-/

section

open Filter
open scoped Pointwise

namespace Green33

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) < A.card ^ 2

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) < A.card ^ 2) →
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) < A.card ^ 2) →
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) < A.card ^ 2) →
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) < A.card ^ 2) →
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) < A.card ^ 2) →
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) < A.card ^ 2) →
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) < A.card ^ 2) →
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≥ A.card ^ 2

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≥ A.card ^ 2) →
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≥ A.card ^ 2) →
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≥ A.card ^ 2) →
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≥ A.card ^ 2) →
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≥ A.card ^ 2) →
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≥ A.card ^ 2) →
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≥ A.card ^ 2) →
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) →
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≥ A.card ^ 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) →
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≥ A.card ^ 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) →
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≥ A.card ^ 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) →
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≥ A.card ^ 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) →
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≥ A.card ^ 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) →
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≥ A.card ^ 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) →
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≥ A.card ^ 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), A.card ^ 2 ≥ (q : ℕ)

set_option maxHeartbeats 200000 in
example (q : ℕ+) (A : Finset (ZMod q)) :
    ((q : ℕ) ≤ A.card ^ 2) ↔ (A.card ^ 2 ≥ (q : ℕ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (q : ℕ+) (A : Finset (ZMod q)) :
    ((q : ℕ) ≤ A.card ^ 2) ↔ (A.card ^ 2 ≥ (q : ℕ)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (q : ℕ+) (A : Finset (ZMod q)) :
    ((q : ℕ) ≤ A.card ^ 2) ↔ (A.card ^ 2 ≥ (q : ℕ)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (q : ℕ+) (A : Finset (ZMod q)) :
    ((q : ℕ) ≤ A.card ^ 2) ↔ (A.card ^ 2 ≥ (q : ℕ)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (q : ℕ+) (A : Finset (ZMod q)) :
    ((q : ℕ) ≤ A.card ^ 2) ↔ (A.card ^ 2 ≥ (q : ℕ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (q : ℕ+) (A : Finset (ZMod q)) :
    ((q : ℕ) ≤ A.card ^ 2) ↔ (A.card ^ 2 ≥ (q : ℕ)) := by
  omega

set_option maxHeartbeats 200000 in
example (q : ℕ+) (A : Finset (ZMod q)) :
    ((q : ℕ) ≤ A.card ^ 2) ↔ (A.card ^ 2 ≥ (q : ℕ)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (q : ℕ+) (A : Finset (ZMod q)) :
    ((q : ℕ) ≤ A.card ^ 2) ↔ (A.card ^ 2 ≥ (q : ℕ)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) ↔
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), A.card ^ 2 ≥ (q : ℕ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) ↔
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), A.card ^ 2 ≥ (q : ℕ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) ↔
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), A.card ^ 2 ≥ (q : ℕ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) ↔
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), A.card ^ 2 ≥ (q : ℕ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℕ+) (A : Finset (ZMod q)) (hA₀ : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) ↔
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA₀ : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) ↔
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA₀ : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) ↔
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA₀ : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) ↔
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA₀ : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), A.card ^ 2 > (q : ℕ)

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), A.card ^ 2 > (q : ℕ)) →
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), A.card ^ 2 > (q : ℕ)) →
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), A.card ^ 2 > (q : ℕ)) →
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), A.card ^ 2 > (q : ℕ)) →
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), A.card ^ 2 > (q : ℕ)) →
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), A.card ^ 2 > (q : ℕ)) →
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), A.card ^ 2 > (q : ℕ)) →
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), A.card ^ 2 ≤ (q : ℕ)

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), A.card ^ 2 ≤ (q : ℕ)) →
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), A.card ^ 2 ≤ (q : ℕ)) →
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), A.card ^ 2 ≤ (q : ℕ)) →
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), A.card ^ 2 ≤ (q : ℕ)) →
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), A.card ^ 2 ≤ (q : ℕ)) →
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), A.card ^ 2 ≤ (q : ℕ)) →
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), A.card ^ 2 ≤ (q : ℕ)) →
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) →
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), A.card ^ 2 ≤ (q : ℕ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) →
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), A.card ^ 2 ≤ (q : ℕ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) →
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), A.card ^ 2 ≤ (q : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) →
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), A.card ^ 2 ≤ (q : ℕ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) →
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), A.card ^ 2 ≤ (q : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) →
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), A.card ^ 2 ≤ (q : ℕ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), (q : ℕ) ≤ A.card ^ 2) →
    (∀ (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ), A.card ^ 2 ≤ (q : ℕ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (q : ℕ+) (A : Finset (ZMod q)) (hA : A + A = Finset.univ) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
