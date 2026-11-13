import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 162

*References:*
- [erdosproblems.com/162](https://www.erdosproblems.com/162)
- [Er90b] Erdős, Paul, *Problems and results on graphs and hypergraphs: similarities and
  differences*. Mathematics of Ramsey theory (1990), 12-28.
-/

section

open Filter Asymptotics

namespace Erdos162

/-- The number of edges of $K_n$ inside `H` that get colour `b` under the colouring `c`. -/
def colourEdgeCount {n : ℕ} (c : Sym2 (Fin n) → Bool) (H : Finset (Fin n)) (b : Bool) : ℕ :=
  (H.sym2.filter (fun e ↦ ¬ e.IsDiag ∧ c e = b)).card

/-- Every set `H` of at least `k` vertices contains more than $\alpha\binom{|H|}{2}$ edges of
each colour under `c`. -/
def IsBalancedAbove (n : ℕ) (α : ℝ) (c : Sym2 (Fin n) → Bool) (k : ℕ) : Prop :=
  ∀ H : Finset (Fin n), k ≤ H.card → ∀ b : Bool,
    α * (H.card.choose 2 : ℝ) < colourEdgeCount c H b

/-- $F(n, \alpha)$: the smallest `k` such that some 2-colouring of $K_n$ satisfies
`IsBalancedAbove n α c k`.

The source says "largest `k`". Read literally, every `k > n` works vacuously, so no largest `k`
exists. The smallest `k` is the reading consistent with the stated $\Theta(\log n)$ growth. -/
noncomputable def F (n : ℕ) (α : ℝ) : ℕ :=
  sInf {k : ℕ | ∃ c : Sym2 (Fin n) → Bool, IsBalancedAbove n α c k}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (h0 : 0 ≤ α), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) :
    (α < 1 / 2) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) :
    (α < 1 / 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) :
    (α < 1 / 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) :
    (α < 1 / 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) :
    (α < 1 / 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) :
    (α < 1 / 2) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) :
    (α < 1 / 2) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 ≤ α) ∧ (¬((α < 1 / 2) ↔ (True))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 ≤ α) ∧ (¬((α < 1 / 2) ↔ (True))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 ≤ α) ∧ (¬((α < 1 / 2) ↔ (True))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 ≤ α) ∧ (¬((α < 1 / 2) ↔ (True))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 ≤ α) ∧ (¬((α < 1 / 2) ↔ (True))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 ≤ α) ∧ (¬((α < 1 / 2) ↔ (True))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α < 1 / 2) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α < 1 / 2) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α < 1 / 2) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α < 1 / 2) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α < 1 / 2) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α < 1 / 2) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) :
    (α < 1 / 2) ↔ (α ≤ 1 / 2) := by
  omega

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) :
    (α < 1 / 2) ↔ (α ≤ 1 / 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) :
    (α < 1 / 2) ↔ (α ≤ 1 / 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) :
    (α < 1 / 2) ↔ (α ≤ 1 / 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) :
    (α < 1 / 2) ↔ (α ≤ 1 / 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) :
    (α < 1 / 2) ↔ (α ≤ 1 / 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) :
    (α < 1 / 2) ↔ (α ≤ 1 / 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 ≤ α) ∧ (¬((α < 1 / 2) ↔ (α ≤ 1 / 2))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 ≤ α) ∧ (¬((α < 1 / 2) ↔ (α ≤ 1 / 2))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 ≤ α) ∧ (¬((α < 1 / 2) ↔ (α ≤ 1 / 2))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 ≤ α) ∧ (¬((α < 1 / 2) ↔ (α ≤ 1 / 2))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 ≤ α) ∧ (¬((α < 1 / 2) ↔ (α ≤ 1 / 2))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 ≤ α) ∧ (¬((α < 1 / 2) ↔ (α ≤ 1 / 2))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α < 1 / 2) ↔ (α ≤ 1 / 2)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α < 1 / 2) ↔ (α ≤ 1 / 2)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α < 1 / 2) ↔ (α ≤ 1 / 2)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α < 1 / 2) ↔ (α ≤ 1 / 2)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α < 1 / 2) ↔ (α ≤ 1 / 2)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α < 1 / 2) ↔ (α ≤ 1 / 2)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 3), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 3), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 3), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 3), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 3), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 3), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 3), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 3), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 3), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 3), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 3), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 3), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 3), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 3), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 3), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) :
    (α < 1 / 2) ↔ (α < 1 / 3) := by
  omega

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) :
    (α < 1 / 2) ↔ (α < 1 / 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) :
    (α < 1 / 2) ↔ (α < 1 / 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) :
    (α < 1 / 2) ↔ (α < 1 / 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) :
    (α < 1 / 2) ↔ (α < 1 / 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) :
    (α < 1 / 2) ↔ (α < 1 / 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) :
    (α < 1 / 2) ↔ (α < 1 / 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 ≤ α) ∧ (¬((α < 1 / 2) ↔ (α < 1 / 3))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 ≤ α) ∧ (¬((α < 1 / 2) ↔ (α < 1 / 3))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 ≤ α) ∧ (¬((α < 1 / 2) ↔ (α < 1 / 3))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 ≤ α) ∧ (¬((α < 1 / 2) ↔ (α < 1 / 3))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 ≤ α) ∧ (¬((α < 1 / 2) ↔ (α < 1 / 3))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 ≤ α) ∧ (¬((α < 1 / 2) ↔ (α < 1 / 3))) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 ≤ α) ∧ (¬((α < 1 / 2) ↔ (α < 1 / 3))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α < 1 / 2) ↔ (α < 1 / 3)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α < 1 / 2) ↔ (α < 1 / 3)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α < 1 / 2) ↔ (α < 1 / 3)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α < 1 / 2) ↔ (α < 1 / 3)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α < 1 / 2) ↔ (α < 1 / 3)) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α < 1 / 2) ↔ (α < 1 / 3)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α < 1 / 2) ↔ (α < 1 / 3)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (h0 : α ≥ 0) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 ≤ α) ↔ (α ≥ 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 ≤ α) ↔ (α ≥ 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 ≤ α) ↔ (α ≥ 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 ≤ α) ↔ (α ≥ 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 ≤ α) ↔ (α ≥ 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 ≤ α) ↔ (α ≥ 0) := by
  omega

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 ≤ α) ↔ (α ≥ 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 ≤ α) ↔ (α ≥ 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) ↔
    (∀ (α : ℝ) (h0 : α ≥ 0) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) ↔
    (∀ (α : ℝ) (h0 : α ≥ 0) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) ↔
    (∀ (α : ℝ) (h0 : α ≥ 0) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) ↔
    (∀ (α : ℝ) (h0 : α ≥ 0) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁₁ c₂ : ℝ, 0 < c₁₁ ∧ c₁₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) ↔ (∃ c₁₁ c₂ : ℝ, 0 < c₁₁ ∧ c₁₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) ↔ (∃ c₁₁ c₂ : ℝ, 0 < c₁₁ ∧ c₁₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) ↔ (∃ c₁₁ c₂ : ℝ, 0 < c₁₁ ∧ c₁₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) ↔ (∃ c₁₁ c₂ : ℝ, 0 < c₁₁ ∧ c₁₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) ↔ (∃ c₁₁ c₂ : ℝ, 0 < c₁₁ ∧ c₁₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) ↔ (∃ c₁₁ c₂ : ℝ, 0 < c₁₁ ∧ c₁₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  omega

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) ↔ (∃ c₁₁ c₂ : ℝ, 0 < c₁₁ ∧ c₁₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) ↔ (∃ c₁₁ c₂ : ℝ, 0 < c₁₁ ∧ c₁₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) ↔
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁₁ c₂ : ℝ, 0 < c₁₁ ∧ c₁₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) ↔
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁₁ c₂ : ℝ, 0 < c₁₁ ∧ c₁₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) ↔
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁₁ c₂ : ℝ, 0 < c₁₁ ∧ c₁₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) ↔
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁₁ c₂ : ℝ, 0 < c₁₁ ∧ c₁₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (h1 : α < 1 / 2) (h0 : 0 ≤ α), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) ↔
    (∀ (α : ℝ) (h1 : α < 1 / 2) (h0 : 0 ≤ α), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) ↔
    (∀ (α : ℝ) (h1 : α < 1 / 2) (h0 : 0 ≤ α), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) ↔
    (∀ (α : ℝ) (h1 : α < 1 / 2) (h0 : 0 ≤ α), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) ↔
    (∀ (α : ℝ) (h1 : α < 1 / 2) (h0 : 0 ≤ α), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (h0' : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) ↔
    (∀ (α : ℝ) (h0' : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) ↔
    (∀ (α : ℝ) (h0' : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) ↔
    (∀ (α : ℝ) (h0' : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) ↔
    (∀ (α : ℝ) (h0' : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (h0 : ¬(α < 0)) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 ≤ α) ↔ (¬(α < 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 ≤ α) ↔ (¬(α < 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 ≤ α) ↔ (¬(α < 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 ≤ α) ↔ (¬(α < 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 ≤ α) ↔ (¬(α < 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 ≤ α) ↔ (¬(α < 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 ≤ α) ↔ (¬(α < 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 ≤ α) ↔ (¬(α < 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) ↔
    (∀ (α : ℝ) (h0 : ¬(α < 0)) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) ↔
    (∀ (α : ℝ) (h0 : ¬(α < 0)) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) ↔
    (∀ (α : ℝ) (h0 : ¬(α < 0)) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) ↔
    (∀ (α : ℝ) (h0 : ¬(α < 0)) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (h0 : α ≥ 0) (h1 : α ≤ 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : α ≥ 0) (h1 : α ≤ 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : α ≥ 0) (h1 : α ≤ 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : α ≥ 0) (h1 : α ≤ 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : α ≥ 0) (h1 : α ≤ 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : α ≥ 0) (h1 : α ≤ 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : α ≥ 0) (h1 : α ≤ 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : α ≥ 0) (h1 : α ≤ 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) :
    (α < 1 / 2) ↔ (α ≤ 1 / 2) := by
  omega

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) :
    (α < 1 / 2) ↔ (α ≤ 1 / 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) :
    (α < 1 / 2) ↔ (α ≤ 1 / 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) :
    (α < 1 / 2) ↔ (α ≤ 1 / 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) :
    (α < 1 / 2) ↔ (α ≤ 1 / 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) :
    (α < 1 / 2) ↔ (α ≤ 1 / 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) :
    (α < 1 / 2) ↔ (α ≤ 1 / 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 ≤ α) ∧ (¬((α < 1 / 2) ↔ (α ≤ 1 / 2))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 ≤ α) ∧ (¬((α < 1 / 2) ↔ (α ≤ 1 / 2))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 ≤ α) ∧ (¬((α < 1 / 2) ↔ (α ≤ 1 / 2))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 ≤ α) ∧ (¬((α < 1 / 2) ↔ (α ≤ 1 / 2))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 ≤ α) ∧ (¬((α < 1 / 2) ↔ (α ≤ 1 / 2))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 ≤ α) ∧ (¬((α < 1 / 2) ↔ (α ≤ 1 / 2))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α < 1 / 2) ↔ (α ≤ 1 / 2)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α < 1 / 2) ↔ (α ≤ 1 / 2)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α < 1 / 2) ↔ (α ≤ 1 / 2)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α < 1 / 2) ↔ (α ≤ 1 / 2)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α < 1 / 2) ↔ (α ≤ 1 / 2)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α < 1 / 2) ↔ (α ≤ 1 / 2)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (h0 : α ≥ 0) (h1 : α < 1 / 3), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : α ≥ 0) (h1 : α < 1 / 3), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : α ≥ 0) (h1 : α < 1 / 3), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : α ≥ 0) (h1 : α < 1 / 3), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : α ≥ 0) (h1 : α < 1 / 3), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : α ≥ 0) (h1 : α < 1 / 3), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : α ≥ 0) (h1 : α < 1 / 3), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : α ≥ 0) (h1 : α < 1 / 3), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : α ≥ 0) (h1 : α < 1 / 3), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : α ≥ 0) (h1 : α < 1 / 3), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : α ≥ 0) (h1 : α < 1 / 3), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : α ≥ 0) (h1 : α < 1 / 3), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : α ≥ 0) (h1 : α < 1 / 3), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : α ≥ 0) (h1 : α < 1 / 3), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : α ≥ 0) (h1 : α < 1 / 3), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) :
    (α < 1 / 2) ↔ (α < 1 / 3) := by
  omega

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) :
    (α < 1 / 2) ↔ (α < 1 / 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) :
    (α < 1 / 2) ↔ (α < 1 / 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) :
    (α < 1 / 2) ↔ (α < 1 / 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) :
    (α < 1 / 2) ↔ (α < 1 / 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) :
    (α < 1 / 2) ↔ (α < 1 / 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) :
    (α < 1 / 2) ↔ (α < 1 / 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 ≤ α) ∧ (¬((α < 1 / 2) ↔ (α < 1 / 3))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 ≤ α) ∧ (¬((α < 1 / 2) ↔ (α < 1 / 3))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 ≤ α) ∧ (¬((α < 1 / 2) ↔ (α < 1 / 3))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 ≤ α) ∧ (¬((α < 1 / 2) ↔ (α < 1 / 3))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 ≤ α) ∧ (¬((α < 1 / 2) ↔ (α < 1 / 3))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 ≤ α) ∧ (¬((α < 1 / 2) ↔ (α < 1 / 3))) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 ≤ α) ∧ (¬((α < 1 / 2) ↔ (α < 1 / 3))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α < 1 / 2) ↔ (α < 1 / 3)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α < 1 / 2) ↔ (α < 1 / 3)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α < 1 / 2) ↔ (α < 1 / 3)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α < 1 / 2) ↔ (α < 1 / 3)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α < 1 / 2) ↔ (α < 1 / 3)) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α < 1 / 2) ↔ (α < 1 / 3)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α < 1 / 2) ↔ (α < 1 / 3)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (h0 : α ≥ 0), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : α ≥ 0), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : α ≥ 0), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : α ≥ 0), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : α ≥ 0), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : α ≥ 0), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : α ≥ 0), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (h0 : α ≥ 0), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) →
    (∀ (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.log n < F n α ∧ (F n α : ℝ) < c₂ * Real.log n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) :
    (α < 1 / 2) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) :
    (α < 1 / 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) :
    (α < 1 / 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) :
    (α < 1 / 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) :
    (α < 1 / 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) :
    (α < 1 / 2) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) :
    (α < 1 / 2) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 ≤ α) ∧ (¬((α < 1 / 2) ↔ (True))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 ≤ α) ∧ (¬((α < 1 / 2) ↔ (True))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 ≤ α) ∧ (¬((α < 1 / 2) ↔ (True))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 ≤ α) ∧ (¬((α < 1 / 2) ↔ (True))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 ≤ α) ∧ (¬((α < 1 / 2) ↔ (True))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 ≤ α) ∧ (¬((α < 1 / 2) ↔ (True))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α < 1 / 2) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α < 1 / 2) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α < 1 / 2) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α < 1 / 2) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α < 1 / 2) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α < 1 / 2) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1 / 2) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
