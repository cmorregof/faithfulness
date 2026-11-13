import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 1173

*Reference:* [erdosproblems.com/1173](https://www.erdosproblems.com/1173)
-/

section

open Cardinal Ordinal

open scoped Cardinal Ordinal

namespace Erdos1173

/-- The **set mapping condition** for `f : ω_{ω+1} → 𝒫(ω_{ω+1})`:
self-avoidance (`α ∉ f α`), image bound (`#(f α) ≤ ℵ_ω`), and almost-disjoint
images (`#(f α ∩ f β) < ℵ_ω` for `α ≠ β`). -/
def IsSetMapping (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) : Prop :=
  (∀ α : (ω_ (ω + 1)).ToType, α ∉ f α) ∧
  (∀ α : (ω_ (ω + 1)).ToType, #(f α) ≤ ℵ_ ω) ∧
  (∀ α β : (ω_ (ω + 1)).ToType, α ≠ β → #(f α ∩ f β : Set (ω_ (ω + 1)).ToType) < ℵ_ ω)

/-- A set `Y ⊆ ω_{ω+1}` is **free** for `f` if for all distinct `α, β ∈ Y`,
`β ∉ f α`. -/
def IsFreeSet (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType)
    (Y : Set (ω_ (ω + 1)).ToType) : Prop :=
  ∀ α ∈ Y, ∀ β ∈ Y, α ≠ β → β ∉ f α

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) ≤ ℵ_ (ω + 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) →
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) ≤ ℵ_ (ω + 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) →
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) ≤ ℵ_ (ω + 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) →
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) ≤ ℵ_ (ω + 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) →
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) ≤ ℵ_ (ω + 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) →
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) ≤ ℵ_ (ω + 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) →
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) ≤ ℵ_ (ω + 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) →
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) ≤ ℵ_ (ω + 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) > ℵ_ (ω + 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) > ℵ_ (ω + 1)) →
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) > ℵ_ (ω + 1)) →
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) > ℵ_ (ω + 1)) →
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) > ℵ_ (ω + 1)) →
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) > ℵ_ (ω + 1)) →
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) > ℵ_ (ω + 1)) →
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) > ℵ_ (ω + 1)) →
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) →
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) > ℵ_ (ω + 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) →
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) > ℵ_ (ω + 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) →
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) > ℵ_ (ω + 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) →
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) > ℵ_ (ω + 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) →
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) > ℵ_ (ω + 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) →
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) > ℵ_ (ω + 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) →
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) > ℵ_ (ω + 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), ℵ_ (ω + 1) > #(f α)

set_option maxHeartbeats 200000 in
example (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (α : (ω_ (ω + 1)).ToType) :
    (#(f α) < ℵ_ (ω + 1)) ↔ (ℵ_ (ω + 1) > #(f α)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (α : (ω_ (ω + 1)).ToType) :
    (#(f α) < ℵ_ (ω + 1)) ↔ (ℵ_ (ω + 1) > #(f α)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (α : (ω_ (ω + 1)).ToType) :
    (#(f α) < ℵ_ (ω + 1)) ↔ (ℵ_ (ω + 1) > #(f α)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (α : (ω_ (ω + 1)).ToType) :
    (#(f α) < ℵ_ (ω + 1)) ↔ (ℵ_ (ω + 1) > #(f α)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (α : (ω_ (ω + 1)).ToType) :
    (#(f α) < ℵ_ (ω + 1)) ↔ (ℵ_ (ω + 1) > #(f α)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (α : (ω_ (ω + 1)).ToType) :
    (#(f α) < ℵ_ (ω + 1)) ↔ (ℵ_ (ω + 1) > #(f α)) := by
  omega

set_option maxHeartbeats 200000 in
example (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (α : (ω_ (ω + 1)).ToType) :
    (#(f α) < ℵ_ (ω + 1)) ↔ (ℵ_ (ω + 1) > #(f α)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (α : (ω_ (ω + 1)).ToType) :
    (#(f α) < ℵ_ (ω + 1)) ↔ (ℵ_ (ω + 1) > #(f α)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) ↔
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), ℵ_ (ω + 1) > #(f α)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) ↔
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), ℵ_ (ω + 1) > #(f α)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) ↔
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), ℵ_ (ω + 1) > #(f α)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) ↔
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), ℵ_ (ω + 1) > #(f α)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf₀ : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) ↔
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf₀ : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) ↔
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf₀ : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) ↔
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf₀ : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) ↔
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf₀ : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), ℵ_ (ω + 1) ≥ #(f α)

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) →
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), ℵ_ (ω + 1) ≥ #(f α)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) →
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), ℵ_ (ω + 1) ≥ #(f α)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) →
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), ℵ_ (ω + 1) ≥ #(f α)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) →
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), ℵ_ (ω + 1) ≥ #(f α)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) →
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), ℵ_ (ω + 1) ≥ #(f α)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) →
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), ℵ_ (ω + 1) ≥ #(f α)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) →
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), ℵ_ (ω + 1) ≥ #(f α)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), ℵ_ (ω + 1) < #(f α)

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), ℵ_ (ω + 1) < #(f α)) →
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), ℵ_ (ω + 1) < #(f α)) →
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), ℵ_ (ω + 1) < #(f α)) →
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), ℵ_ (ω + 1) < #(f α)) →
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), ℵ_ (ω + 1) < #(f α)) →
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), ℵ_ (ω + 1) < #(f α)) →
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), ℵ_ (ω + 1) < #(f α)) →
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) →
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), ℵ_ (ω + 1) < #(f α)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) →
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), ℵ_ (ω + 1) < #(f α)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) →
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), ℵ_ (ω + 1) < #(f α)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) →
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), ℵ_ (ω + 1) < #(f α)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) →
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), ℵ_ (ω + 1) < #(f α)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) →
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), ℵ_ (ω + 1) < #(f α)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), #(f α) < ℵ_ (ω + 1)) →
    (∀ (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) (α : (ω_ (ω + 1)).ToType), ℵ_ (ω + 1) < #(f α)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (α : (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (α : (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (α : (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (α : (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (f : (ω_ (ω + 1)).ToType → Set (ω_ (ω + 1)).ToType) (α : (ω_ (ω + 1)).ToType) (hf : IsSetMapping f) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
