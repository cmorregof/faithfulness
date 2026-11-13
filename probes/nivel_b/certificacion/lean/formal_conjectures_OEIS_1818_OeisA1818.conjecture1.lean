import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Squares of double factorials

Squares of double factorials: $a(n) = ((2n-1)!!)^2 = (1 \cdot 3 \cdot 5 \cdots (2n-1))^2$.

*References:*
- [A001818](https://oeis.org/A001818)
- [She, Sun, Xia, *A novel permanent identity with applications*, Theorem 1.3(ii)](https://arxiv.org/abs/2208.12167)
- [Yang, Zhang, *Sun-type determinant and permanent congruences*, Proposition 17](https://arxiv.org/abs/2605.19502)
-/

section

namespace OeisA1818

/-- The sequence of squares of double factorials: $a(n) = ((2n-1)!!)^2$. -/
def a (n : ℕ) : ℕ :=
  (∏ k ∈ Finset.range n, (2 * k + 1)) ^ 2

/-- Characteristic function $f(j, k)$ for matrix entries in $\mathbb{Z}/p^2\mathbb{Z}$. -/
noncomputable def fEntry {p : ℕ} (i j : ℕ) : ZMod (p ^ 2) :=
  let R := ZMod (p ^ 2)
  if i = j then
    1
  else
    let iInt : ℤ := i
    let jInt : ℤ := j
    let num : R := (iInt + jInt : ℤ)
    let den : R := (iInt - jInt : ℤ)
    num * den⁻¹

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : 1 < n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : 1 < n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : 1 < n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : 1 < n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : 1 < n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : 1 < n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : 1 < n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
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
  ∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) ↔ (∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) ↔ (∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) ↔ (∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) ↔ (∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) ↔ (∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) ↔ (∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) ↔ (∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 1), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)

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
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) ↔
    (∀ (n : ℕ) (hn : n ≥ 1), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) ↔
    (∀ (n : ℕ) (hn : n ≥ 1), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) ↔
    (∀ (n : ℕ) (hn : n ≥ 1), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) ↔
    (∀ (n : ℕ) (hn : n ≥ 1), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn₀ : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) ↔
    (∀ (n : ℕ) (hn₀ : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) ↔
    (∀ (n : ℕ) (hn₀ : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) ↔
    (∀ (n : ℕ) (hn₀ : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) ↔
    (∀ (n : ℕ) (hn₀ : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : ¬(n < 1)), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)

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
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) ↔
    (∀ (n : ℕ) (hn : ¬(n < 1)), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) ↔
    (∀ (n : ℕ) (hn : ¬(n < 1)), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) ↔
    (∀ (n : ℕ) (hn : ¬(n < 1)), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) ↔
    (∀ (n : ℕ) (hn : ¬(n < 1)), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)

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
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) ↔
    (∀ (n : ℕ) (hn : 0 < n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) ↔
    (∀ (n : ℕ) (hn : 0 < n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) ↔
    (∀ (n : ℕ) (hn : 0 < n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) ↔
    (∀ (n : ℕ) (hn : 0 < n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 1), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : n > 1), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : n > 1), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : n > 1), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : n > 1), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : n > 1), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : n > 1), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : n > 1), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
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
  ∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 1), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : n ≥ 1), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : n ≥ 1), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : n ≥ 1), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : n ≥ 1), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : n ≥ 1), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : n ≥ 1), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : n ≥ 1), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) ↔ (∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) ↔ (∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) ↔ (∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) ↔ (∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) ↔ (∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) ↔ (∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) ↔ (∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : 0 < n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : 0 < n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : 0 < n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : 0 < n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : 0 < n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : 0 < n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) →
    (∀ (n : ℕ) (hn : 0 < n), ∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) ↔ (∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) ↔ (∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) ↔ (∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) ↔ (∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) ↔ (∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) ↔ (∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ)) ↔ (∀ (ζ : ℂ), IsPrimitiveRoot ζ (3 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ))) :=
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
