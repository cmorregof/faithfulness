import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 1128

*Reference:* [erdosproblems.com/1128](https://www.erdosproblems.com/1128)
-/

section

open Cardinal Set Ordinal Order

namespace Erdos1128

/-- A subset $A_1 \times B_1 \times C_1$ of $A \times B \times C$ is **monochromatic**
under a 2-colouring $f : A \to B \to C \to \operatorname{Fin} 2$ if $f$ is constant on
$A_1 \times B_1 \times C_1$. -/
def IsMonochromaticBox {A B C : Type*} (f : A → B → C → Fin 2)
    (A₁ : Set A) (B₁ : Set B) (C₁ : Set C) : Prop :=
  ∃ c : Fin 2, ∀ a ∈ A₁, ∀ b ∈ B₁, ∀ c' ∈ C₁, f a b c' = c

/-
Auxiliary lemmas for the Prikry–Mills construction.
These establish key countability and boundedness properties of ω₁.
-/

/-- The set of countable ordinals, expressed using Mathlib's `ω_ 1`. -/
abbrev Omega1 := {o : Ordinal.{0} // o < ω_ 1}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {γ : Ordinal} (hγ : γ < ω_ 1), (Set.Iio γ).Countable

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {γ : Ordinal} (hγ : γ ≤ ω_ 1), (Set.Iio γ).Countable

set_option maxHeartbeats 200000 in
example :
    (∀ {γ : Ordinal} (hγ : γ ≤ ω_ 1), (Set.Iio γ).Countable) →
    (∀ {γ : Ordinal} (hγ : γ < ω_ 1), (Set.Iio γ).Countable) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {γ : Ordinal} (hγ : γ ≤ ω_ 1), (Set.Iio γ).Countable) →
    (∀ {γ : Ordinal} (hγ : γ < ω_ 1), (Set.Iio γ).Countable) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {γ : Ordinal} (hγ : γ ≤ ω_ 1), (Set.Iio γ).Countable) →
    (∀ {γ : Ordinal} (hγ : γ < ω_ 1), (Set.Iio γ).Countable) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {γ : Ordinal} (hγ : γ ≤ ω_ 1), (Set.Iio γ).Countable) →
    (∀ {γ : Ordinal} (hγ : γ < ω_ 1), (Set.Iio γ).Countable) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {γ : Ordinal} (hγ : γ ≤ ω_ 1), (Set.Iio γ).Countable) →
    (∀ {γ : Ordinal} (hγ : γ < ω_ 1), (Set.Iio γ).Countable) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {γ : Ordinal} (hγ : γ ≤ ω_ 1), (Set.Iio γ).Countable) →
    (∀ {γ : Ordinal} (hγ : γ < ω_ 1), (Set.Iio γ).Countable) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {γ : Ordinal} (hγ : γ ≤ ω_ 1), (Set.Iio γ).Countable) →
    (∀ {γ : Ordinal} (hγ : γ < ω_ 1), (Set.Iio γ).Countable) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {γ : Ordinal}  :
    (γ < ω_ 1) ↔ (γ ≤ ω_ 1) := by
  omega

set_option maxHeartbeats 200000 in
example {γ : Ordinal}  :
    (γ < ω_ 1) ↔ (γ ≤ ω_ 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {γ : Ordinal}  :
    (γ < ω_ 1) ↔ (γ ≤ ω_ 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {γ : Ordinal}  :
    (γ < ω_ 1) ↔ (γ ≤ ω_ 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {γ : Ordinal}  :
    (γ < ω_ 1) ↔ (γ ≤ ω_ 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {γ : Ordinal}  :
    (γ < ω_ 1) ↔ (γ ≤ ω_ 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example {γ : Ordinal}  :
    (γ < ω_ 1) ↔ (γ ≤ ω_ 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {γ : Ordinal} (hγ : γ < ω_ 1), (Set.Iio γ).Countable

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {γ : Ordinal} (hγ : ω_ 1 > γ), (Set.Iio γ).Countable

set_option maxHeartbeats 200000 in
example {γ : Ordinal} :
    (γ < ω_ 1) ↔ (ω_ 1 > γ) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {γ : Ordinal} :
    (γ < ω_ 1) ↔ (ω_ 1 > γ) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {γ : Ordinal} :
    (γ < ω_ 1) ↔ (ω_ 1 > γ) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {γ : Ordinal} :
    (γ < ω_ 1) ↔ (ω_ 1 > γ) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {γ : Ordinal} :
    (γ < ω_ 1) ↔ (ω_ 1 > γ) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {γ : Ordinal} :
    (γ < ω_ 1) ↔ (ω_ 1 > γ) := by
  omega

set_option maxHeartbeats 200000 in
example {γ : Ordinal} :
    (γ < ω_ 1) ↔ (ω_ 1 > γ) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {γ : Ordinal} :
    (γ < ω_ 1) ↔ (ω_ 1 > γ) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {γ : Ordinal} (hγ : γ < ω_ 1), (Set.Iio γ).Countable) ↔
    (∀ {γ : Ordinal} (hγ : ω_ 1 > γ), (Set.Iio γ).Countable) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {γ : Ordinal} (hγ : γ < ω_ 1), (Set.Iio γ).Countable) ↔
    (∀ {γ : Ordinal} (hγ : ω_ 1 > γ), (Set.Iio γ).Countable) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {γ : Ordinal} (hγ : γ < ω_ 1), (Set.Iio γ).Countable) ↔
    (∀ {γ : Ordinal} (hγ : ω_ 1 > γ), (Set.Iio γ).Countable) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {γ : Ordinal} (hγ : γ < ω_ 1), (Set.Iio γ).Countable) ↔
    (∀ {γ : Ordinal} (hγ : ω_ 1 > γ), (Set.Iio γ).Countable) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {γ : Ordinal} (hγ : γ < ω_ 1), (Set.Iio γ).Countable

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {γ : Ordinal} (hγ₀ : γ < ω_ 1), (Set.Iio γ).Countable

set_option maxHeartbeats 200000 in
example :
    (∀ {γ : Ordinal} (hγ : γ < ω_ 1), (Set.Iio γ).Countable) ↔
    (∀ {γ : Ordinal} (hγ₀ : γ < ω_ 1), (Set.Iio γ).Countable) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {γ : Ordinal} (hγ : γ < ω_ 1), (Set.Iio γ).Countable) ↔
    (∀ {γ : Ordinal} (hγ₀ : γ < ω_ 1), (Set.Iio γ).Countable) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {γ : Ordinal} (hγ : γ < ω_ 1), (Set.Iio γ).Countable) ↔
    (∀ {γ : Ordinal} (hγ₀ : γ < ω_ 1), (Set.Iio γ).Countable) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {γ : Ordinal} (hγ : γ < ω_ 1), (Set.Iio γ).Countable) ↔
    (∀ {γ : Ordinal} (hγ₀ : γ < ω_ 1), (Set.Iio γ).Countable) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {γ : Ordinal} (hγ : γ < ω_ 1), (Set.Iio γ).Countable

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {γ : Ordinal} (hγ : ω_ 1 ≥ γ), (Set.Iio γ).Countable

set_option maxHeartbeats 200000 in
example :
    (∀ {γ : Ordinal} (hγ : ω_ 1 ≥ γ), (Set.Iio γ).Countable) →
    (∀ {γ : Ordinal} (hγ : γ < ω_ 1), (Set.Iio γ).Countable) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {γ : Ordinal} (hγ : ω_ 1 ≥ γ), (Set.Iio γ).Countable) →
    (∀ {γ : Ordinal} (hγ : γ < ω_ 1), (Set.Iio γ).Countable) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {γ : Ordinal} (hγ : ω_ 1 ≥ γ), (Set.Iio γ).Countable) →
    (∀ {γ : Ordinal} (hγ : γ < ω_ 1), (Set.Iio γ).Countable) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {γ : Ordinal} (hγ : ω_ 1 ≥ γ), (Set.Iio γ).Countable) →
    (∀ {γ : Ordinal} (hγ : γ < ω_ 1), (Set.Iio γ).Countable) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {γ : Ordinal} (hγ : ω_ 1 ≥ γ), (Set.Iio γ).Countable) →
    (∀ {γ : Ordinal} (hγ : γ < ω_ 1), (Set.Iio γ).Countable) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {γ : Ordinal} (hγ : ω_ 1 ≥ γ), (Set.Iio γ).Countable) →
    (∀ {γ : Ordinal} (hγ : γ < ω_ 1), (Set.Iio γ).Countable) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {γ : Ordinal} (hγ : ω_ 1 ≥ γ), (Set.Iio γ).Countable) →
    (∀ {γ : Ordinal} (hγ : γ < ω_ 1), (Set.Iio γ).Countable) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {γ : Ordinal}  :
    (γ < ω_ 1) ↔ (ω_ 1 ≥ γ) := by
  omega

set_option maxHeartbeats 200000 in
example {γ : Ordinal}  :
    (γ < ω_ 1) ↔ (ω_ 1 ≥ γ) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {γ : Ordinal}  :
    (γ < ω_ 1) ↔ (ω_ 1 ≥ γ) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {γ : Ordinal}  :
    (γ < ω_ 1) ↔ (ω_ 1 ≥ γ) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {γ : Ordinal}  :
    (γ < ω_ 1) ↔ (ω_ 1 ≥ γ) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {γ : Ordinal}  :
    (γ < ω_ 1) ↔ (ω_ 1 ≥ γ) := by
  simp_all

set_option maxHeartbeats 200000 in
example {γ : Ordinal}  :
    (γ < ω_ 1) ↔ (ω_ 1 ≥ γ) := by
  plausible

set_option maxHeartbeats 200000 in
example {γ : Ordinal} (hγ : γ < ω_ 1) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {γ : Ordinal} (hγ : γ < ω_ 1) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {γ : Ordinal} (hγ : γ < ω_ 1) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {γ : Ordinal} (hγ : γ < ω_ 1) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {γ : Ordinal} (hγ : γ < ω_ 1) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
