import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Bounds on fractional parts $n r^2 - a(n)$ for $r = (2+\sqrt{5})/2$

$a(n) = \lfloor r \cdot \lfloor r \cdot n \rfloor \rfloor$, where $r = (2 + \sqrt{5})/2$.

*References:*
- [A341254](https://oeis.org/A341254)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/

section

namespace OeisA341254

open Real

/-- The constant $r = (2 + \sqrt{5})/2$. -/
noncomputable def rConst : ℝ := (2 + sqrt 5) / 2

/-- The constant $r^2$. -/
noncomputable def rSq : ℝ := rConst * rConst

/--
$a(n) = \lfloor r \cdot \lfloor r \cdot n \rfloor \rfloor$, where $r = (2 + \sqrt{5})/2$.
Note: The original OEIS definition has $n$ starting at 1. We define $a(n)$ for all $\mathbb{N}$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let r := rConst
  let inner_floor : ℤ := Int.floor (r * n)
  (Int.floor (r * inner_floor.cast)).toNat

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 < n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 < n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 < n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 < n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 < n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 < n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 < n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (1 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (1 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (1 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (1 < n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (1 < n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (1 < n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (1 < n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (1 < n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (1 < n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔ ((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔ ((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔ ((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔ ((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔ ((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔ ((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔ ((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), (1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔ ((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔ ((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔ ((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔ ((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔ ((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔ ((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔ ((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔ ((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 1), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (n ≥ 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (n ≥ 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (n ≥ 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (n ≥ 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (n ≥ 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (n ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (n ≥ 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (n ≥ 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔
    (∀ (n : ℕ) (hn : n ≥ 1), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔
    (∀ (n : ℕ) (hn : n ≥ 1), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔
    (∀ (n : ℕ) (hn : n ≥ 1), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔
    (∀ (n : ℕ) (hn : n ≥ 1), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), (n : ℝ) * rSq - (a n : ℝ) < 3 ∧ (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ)

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔ ((n : ℝ) * rSq - (a n : ℝ) < 3 ∧ (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔ ((n : ℝ) * rSq - (a n : ℝ) < 3 ∧ (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔ ((n : ℝ) * rSq - (a n : ℝ) < 3 ∧ (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔ ((n : ℝ) * rSq - (a n : ℝ) < 3 ∧ (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔ ((n : ℝ) * rSq - (a n : ℝ) < 3 ∧ (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔ ((n : ℝ) * rSq - (a n : ℝ) < 3 ∧ (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔ ((n : ℝ) * rSq - (a n : ℝ) < 3 ∧ (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔ ((n : ℝ) * rSq - (a n : ℝ) < 3 ∧ (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n), (n : ℝ) * rSq - (a n : ℝ) < 3 ∧ (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n), (n : ℝ) * rSq - (a n : ℝ) < 3 ∧ (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n), (n : ℝ) * rSq - (a n : ℝ) < 3 ∧ (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n), (n : ℝ) * rSq - (a n : ℝ) < 3 ∧ (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn₀ : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔
    (∀ (n : ℕ) (hn₀ : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔
    (∀ (n : ℕ) (hn₀ : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔
    (∀ (n : ℕ) (hn₀ : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔
    (∀ (n : ℕ) (hn₀ : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : ¬(n < 1)), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔
    (∀ (n : ℕ) (hn : ¬(n < 1)), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔
    (∀ (n : ℕ) (hn : ¬(n < 1)), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔
    (∀ (n : ℕ) (hn : ¬(n < 1)), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔
    (∀ (n : ℕ) (hn : ¬(n < 1)), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (0 < n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (0 < n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (0 < n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (0 < n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (0 < n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (0 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (0 < n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (0 < n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔
    (∀ (n : ℕ) (hn : 0 < n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔
    (∀ (n : ℕ) (hn : 0 < n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔
    (∀ (n : ℕ) (hn : 0 < n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔
    (∀ (n : ℕ) (hn : 0 < n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 1), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : n > 1), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : n > 1), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : n > 1), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : n > 1), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : n > 1), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : n > 1), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : n > 1), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (n > 1) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (n > 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (n > 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (n > 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (n > 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (n > 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (n > 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (n > 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (n > 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (n > 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (n > 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (n > 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (n > 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 1), (1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), (1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), (1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), (1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), (1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), (1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), (1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), (1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : n ≥ 1), (1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : n ≥ 1), (1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : n ≥ 1), (1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : n ≥ 1), (1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : n ≥ 1), (1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : n ≥ 1), (1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : n ≥ 1), (1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔ ((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔ ((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔ ((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔ ((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔ ((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔ ((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔ ((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔ ((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), (1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), (1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), (1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), (1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), (1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), (1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), (1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), (1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 0 < n), (1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 0 < n), (1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 0 < n), (1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 0 < n), (1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 0 < n), (1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 0 < n), (1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 0 < n), (1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔ ((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔ ((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔ ((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔ ((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔ ((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔ ((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔ ((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔ ((1 / 5 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), (n : ℝ) * rSq - (a n : ℝ) < 3

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) →
    (∀ (n : ℕ) (hn : 1 ≤ n), (n : ℝ) * rSq - (a n : ℝ) < 3) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔ ((n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔ ((n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔ ((n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔ ((n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔ ((n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔ ((n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3) ↔ ((n : ℝ) * rSq - (a n : ℝ) < 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 ≤ n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 ≤ n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 ≤ n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 ≤ n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 ≤ n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
