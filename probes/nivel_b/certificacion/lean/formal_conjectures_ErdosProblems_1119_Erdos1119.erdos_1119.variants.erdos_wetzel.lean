import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 1119

*References:*
- [erdosproblems.com/1119](https://www.erdosproblems.com/1119)
- [Ha74] Hayman, W. K., Research problems in function theory: new problems. (1974), 155--180.
- [Er64g] Erdős, P., An interpolation problem associated with the continuum hypothesis.
  Michigan Math. J. (1964), 9--10.
- [KuSh17] Kumar, Ashutosh and Shelah, Saharon, On a question about families of entire
  functions. Fund. Math. (2017), 279--288.
- [ScWe24] Schilhan, Jonathan and Weinert, Thilo, Wetzel families and the continuum.
  J. Lond. Math. Soc. (2) (2024), Paper No. e12918, 27.
-/

section

open Cardinal Order
open scoped Cardinal

namespace Erdos1119

/-
**Independence of Erdős Problem 1119** (prose record; consistency statements about
models of ZFC are not directly formalizable inside Lean's fixed model):

* Kumar–Shelah [KuSh17] constructed a model of ZFC with $\mathfrak{c} = \aleph_2$ in
  which every family of entire functions taking at most $\aleph_1$ values at each point
  has cardinality at most $\aleph_1$ — so the answer to the problem is **yes** in that
  model (with $\mathfrak{m} = \aleph_1$).
* Schilhan–Weinert [ScWe24] constructed a different model of ZFC with
  $\mathfrak{c} = \aleph_2$ containing a family of $\aleph_2$ entire functions taking at
  most $\aleph_1$ values at each point — so the answer is **no** in that model.

Together with the easy case $\mathfrak{m}^+ < \mathfrak{c}$ below, these show the
problem is independent of ZFC, with the only undecidable case being
$\mathfrak{m}^+ = \mathfrak{c}$.
-/

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable

set_option maxHeartbeats 200000 in
example :
    (∀ (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) →
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) →
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) →
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) →
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) →
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) →
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) →
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) :
    (ℵ_ 1 < 𝔠) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) :
    (ℵ_ 1 < 𝔠) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) :
    (ℵ_ 1 < 𝔠) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) :
    (ℵ_ 1 < 𝔠) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) :
    (ℵ_ 1 < 𝔠) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) :
    (ℵ_ 1 < 𝔠) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) :
    (ℵ_ 1 < 𝔠) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ¬((ℵ_ 1 < 𝔠) ↔ (True)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((ℵ_ 1 < 𝔠) ↔ (True)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h : ℵ_ 1 ≤ 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable

set_option maxHeartbeats 200000 in
example :
    (∀ (h : ℵ_ 1 ≤ 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) →
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h : ℵ_ 1 ≤ 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) →
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h : ℵ_ 1 ≤ 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) →
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (h : ℵ_ 1 ≤ 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) →
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h : ℵ_ 1 ≤ 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) →
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (h : ℵ_ 1 ≤ 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) →
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (h : ℵ_ 1 ≤ 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) →
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) :
    (ℵ_ 1 < 𝔠) ↔ (ℵ_ 1 ≤ 𝔠) := by
  omega

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) :
    (ℵ_ 1 < 𝔠) ↔ (ℵ_ 1 ≤ 𝔠) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) :
    (ℵ_ 1 < 𝔠) ↔ (ℵ_ 1 ≤ 𝔠) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) :
    (ℵ_ 1 < 𝔠) ↔ (ℵ_ 1 ≤ 𝔠) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) :
    (ℵ_ 1 < 𝔠) ↔ (ℵ_ 1 ≤ 𝔠) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) :
    (ℵ_ 1 < 𝔠) ↔ (ℵ_ 1 ≤ 𝔠) := by
  simp_all

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) :
    (ℵ_ 1 < 𝔠) ↔ (ℵ_ 1 ≤ 𝔠) := by
  plausible

set_option maxHeartbeats 200000 in
example : ¬((ℵ_ 1 < 𝔠) ↔ (ℵ_ 1 ≤ 𝔠)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((ℵ_ 1 < 𝔠) ↔ (ℵ_ 1 ≤ 𝔠)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h : 𝔠 > ℵ_ 1) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) :
    (ℵ_ 1 < 𝔠) ↔ (𝔠 > ℵ_ 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) :
    (ℵ_ 1 < 𝔠) ↔ (𝔠 > ℵ_ 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) :
    (ℵ_ 1 < 𝔠) ↔ (𝔠 > ℵ_ 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) :
    (ℵ_ 1 < 𝔠) ↔ (𝔠 > ℵ_ 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) :
    (ℵ_ 1 < 𝔠) ↔ (𝔠 > ℵ_ 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) :
    (ℵ_ 1 < 𝔠) ↔ (𝔠 > ℵ_ 1) := by
  omega

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) :
    (ℵ_ 1 < 𝔠) ↔ (𝔠 > ℵ_ 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) :
    (ℵ_ 1 < 𝔠) ↔ (𝔠 > ℵ_ 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) ↔
    (∀ (h : 𝔠 > ℵ_ 1) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) ↔
    (∀ (h : 𝔠 > ℵ_ 1) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) ↔
    (∀ (h : 𝔠 > ℵ_ 1) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) ↔
    (∀ (h : 𝔠 > ℵ_ 1) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) (hF : ∀ f ∈ F, Differentiable ℂ f), F.Countable

set_option maxHeartbeats 200000 in
example :
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) ↔
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) (hF : ∀ f ∈ F, Differentiable ℂ f), F.Countable) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) ↔
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) (hF : ∀ f ∈ F, Differentiable ℂ f), F.Countable) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) ↔
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) (hF : ∀ f ∈ F, Differentiable ℂ f), F.Countable) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) ↔
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) (hF : ∀ f ∈ F, Differentiable ℂ f), F.Countable) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h₀ : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable

set_option maxHeartbeats 200000 in
example :
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) ↔
    (∀ (h₀ : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) ↔
    (∀ (h₀ : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) ↔
    (∀ (h₀ : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) ↔
    (∀ (h₀ : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h : ¬(𝔠 ≤ ℵ_ 1)) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) :
    (ℵ_ 1 < 𝔠) ↔ (¬(𝔠 ≤ ℵ_ 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) :
    (ℵ_ 1 < 𝔠) ↔ (¬(𝔠 ≤ ℵ_ 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) :
    (ℵ_ 1 < 𝔠) ↔ (¬(𝔠 ≤ ℵ_ 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) :
    (ℵ_ 1 < 𝔠) ↔ (¬(𝔠 ≤ ℵ_ 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) :
    (ℵ_ 1 < 𝔠) ↔ (¬(𝔠 ≤ ℵ_ 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) :
    (ℵ_ 1 < 𝔠) ↔ (¬(𝔠 ≤ ℵ_ 1)) := by
  omega

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) :
    (ℵ_ 1 < 𝔠) ↔ (¬(𝔠 ≤ ℵ_ 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) :
    (ℵ_ 1 < 𝔠) ↔ (¬(𝔠 ≤ ℵ_ 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) ↔
    (∀ (h : ¬(𝔠 ≤ ℵ_ 1)) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) ↔
    (∀ (h : ¬(𝔠 ≤ ℵ_ 1)) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) ↔
    (∀ (h : ¬(𝔠 ≤ ℵ_ 1)) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) ↔
    (∀ (h : ¬(𝔠 ≤ ℵ_ 1)) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h : 𝔠 ≥ ℵ_ 1) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable

set_option maxHeartbeats 200000 in
example :
    (∀ (h : 𝔠 ≥ ℵ_ 1) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) →
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h : 𝔠 ≥ ℵ_ 1) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) →
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h : 𝔠 ≥ ℵ_ 1) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) →
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (h : 𝔠 ≥ ℵ_ 1) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) →
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h : 𝔠 ≥ ℵ_ 1) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) →
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (h : 𝔠 ≥ ℵ_ 1) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) →
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (h : 𝔠 ≥ ℵ_ 1) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) →
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) :
    (ℵ_ 1 < 𝔠) ↔ (𝔠 ≥ ℵ_ 1) := by
  omega

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) :
    (ℵ_ 1 < 𝔠) ↔ (𝔠 ≥ ℵ_ 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) :
    (ℵ_ 1 < 𝔠) ↔ (𝔠 ≥ ℵ_ 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) :
    (ℵ_ 1 < 𝔠) ↔ (𝔠 ≥ ℵ_ 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) :
    (ℵ_ 1 < 𝔠) ↔ (𝔠 ≥ ℵ_ 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) :
    (ℵ_ 1 < 𝔠) ↔ (𝔠 ≥ ℵ_ 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) :
    (ℵ_ 1 < 𝔠) ↔ (𝔠 ≥ ℵ_ 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ¬((ℵ_ 1 < 𝔠) ↔ (𝔠 ≥ ℵ_ 1)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((ℵ_ 1 < 𝔠) ↔ (𝔠 ≥ ℵ_ 1)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (F : Set (ℂ → ℂ)) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) (hF : ∀ f ∈ F, Differentiable ℂ f), F.Countable

set_option maxHeartbeats 200000 in
example :
    (∀ (F : Set (ℂ → ℂ)) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) (hF : ∀ f ∈ F, Differentiable ℂ f), F.Countable) →
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (F : Set (ℂ → ℂ)) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) (hF : ∀ f ∈ F, Differentiable ℂ f), F.Countable) →
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (F : Set (ℂ → ℂ)) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) (hF : ∀ f ∈ F, Differentiable ℂ f), F.Countable) →
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (F : Set (ℂ → ℂ)) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) (hF : ∀ f ∈ F, Differentiable ℂ f), F.Countable) →
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (F : Set (ℂ → ℂ)) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) (hF : ∀ f ∈ F, Differentiable ℂ f), F.Countable) →
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (F : Set (ℂ → ℂ)) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) (hF : ∀ f ∈ F, Differentiable ℂ f), F.Countable) →
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (F : Set (ℂ → ℂ)) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) (hF : ∀ f ∈ F, Differentiable ℂ f), F.Countable) →
    (∀ (h : ℵ_ 1 < 𝔠) (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable), F.Countable) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) :
    (ℵ_ 1 < 𝔠) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) :
    (ℵ_ 1 < 𝔠) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) :
    (ℵ_ 1 < 𝔠) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) :
    (ℵ_ 1 < 𝔠) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) :
    (ℵ_ 1 < 𝔠) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) :
    (ℵ_ 1 < 𝔠) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) :
    (ℵ_ 1 < 𝔠) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ¬((ℵ_ 1 < 𝔠) ↔ (True)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((ℵ_ 1 < 𝔠) ↔ (True)) :=
  by decide

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) (h : ℵ_ 1 < 𝔠) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) (h : ℵ_ 1 < 𝔠) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) (h : ℵ_ 1 < 𝔠) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) (h : ℵ_ 1 < 𝔠) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (F : Set (ℂ → ℂ)) (h : ℵ_ 1 < 𝔠) (hF : ∀ f ∈ F, Differentiable ℂ f) (hval : ∀ z₀ : ℂ, {y : ℂ | ∃ f ∈ F, f z₀ = y}.Countable) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
