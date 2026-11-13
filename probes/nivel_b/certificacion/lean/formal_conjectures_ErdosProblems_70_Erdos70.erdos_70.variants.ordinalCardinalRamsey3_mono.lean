import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Data.Set.Triplewise
/-!
# Erdős Problem 70

*References:*
- [erdosproblems.com/70](https://www.erdosproblems.com/70)
- [ErRa56] Erdős, P. and Rado, R., *A partition calculus in set theory*,
  Bull. Amer. Math. Soc. **62** (1956), 427–489, Theorem 31.
- [Er87] Erdős, P., *Some problems on finite and infinite graphs*,
  Logic and combinatorics (Arcata, Calif., 1985), Contemp. Math. **65** (1987), 223–228.

The 3-uniform (triple) partition relation $\mathfrak{c} \to (\beta, n)^3_2$, where
$\mathfrak{c}$ denotes the order type of the real numbers with their usual order (written
$\lambda$ in [ErRa56]). This is the triple analogue of `OrdinalCardinalRamsey` used in
Problems 590–592; the file also contains the analogous relation for an ordinal in place
of the real line.
-/

section

open Cardinal Ordinal
open scoped Cardinal

namespace Erdos70

universe u

/- ### The 3-uniform partition relation -/

/--
`OrdinalCardinalRamsey3 α β c` asserts the 3-uniform ordinal Ramsey property
$\alpha \to (\beta, c)^3_2$.

It states that for any 2-coloring of all 3-element subsets of (the ordinal type) $\alpha$,
one of the following must hold:
* There is a red-monochromatic subset of order type $\beta$: every 3-element sub-subset is
  colored red. (Formally: a set $s \subseteq \alpha$ with $\operatorname{typeLT} s = \beta$
  such that any three distinct elements of $s$ are colored red.)
* There is a blue-monochromatic subset of cardinality $c$: a set $s \subseteq \alpha$ with
  $\#s = c$ such that every three distinct elements of $s$ are colored blue.

The coloring is given as a predicate `isRed : α.ToType → α.ToType → α.ToType → Prop` on
ordered triples of distinct elements; to faithfully encode a coloring of *unordered*
3-element subsets we additionally require `isRed` to be invariant under permutation of
its three (distinct) arguments.
-/
def OrdinalCardinalRamsey3 (α β : Ordinal.{u}) (c : Cardinal.{u}) : Prop :=
  -- For any partition of 3-element subsets into red and blue:
  ∀ (isRed : α.ToType → α.ToType → α.ToType → Prop),
    -- The colouring is well-defined on *unordered* triples of distinct elements:
    (∀ x y z, x ≠ y → y ≠ z → x ≠ z →
      (isRed x y z ↔ isRed y x z) ∧ (isRed x y z ↔ isRed x z y)) →
    -- either there is a red-monochromatic subset of order type β
    (∃ s : Set α.ToType, typeLT s = β ∧ s.Triplewise isRed) ∨
    -- or there is a blue-monochromatic subset of cardinality c
    (∃ s : Set α.ToType, #s = c ∧ s.Triplewise (fun x y z ↦ ¬ isRed x y z))

/--
`RealCardinalRamsey3 β c` asserts the 3-uniform partition relation
$\mathfrak{c} \to (\beta, c)^3_2$, where $\mathfrak{c}$ is the order type of the real
numbers with their usual order.

It states that for any 2-coloring of all 3-element subsets of $\mathbb{R}$,
one of the following must hold:
* There is a red-monochromatic subset of order type $\beta$: the range of an order embedding
  `β.ToType ↪o ℝ` such that any three distinct elements of the range are colored red.
* There is a blue-monochromatic subset of cardinality $c$: a set $s \subseteq \mathbb{R}$ with
  $\#s = c$ such that every three distinct elements of $s$ are colored blue.

The coloring is encoded as in `OrdinalCardinalRamsey3`: a predicate on ordered triples of
distinct reals that is invariant under permutation of its three arguments.
-/
def RealCardinalRamsey3 (β : Ordinal.{0}) (c : Cardinal.{0}) : Prop :=
  -- For any partition of 3-element subsets of `ℝ` into red and blue:
  ∀ (isRed : ℝ → ℝ → ℝ → Prop),
    -- The colouring is well-defined on *unordered* triples of distinct elements:
    (∀ x y z, x ≠ y → y ≠ z → x ≠ z →
      (isRed x y z ↔ isRed y x z) ∧ (isRed x y z ↔ isRed x z y)) →
    -- either there is a red-monochromatic subset of order type β
    (∃ e : β.ToType ↪o ℝ, (Set.range e).Triplewise isRed) ∨
    -- or there is a blue-monochromatic subset of cardinality c
    (∃ s : Set ℝ, #s = c ∧ s.Triplewise (fun x y z ↦ ¬ isRed x y z))

/- ### The main open problem -/

/- ### Variants -/

namespace erdos_70.variants

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c'

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β), OrdinalCardinalRamsey3 α β' c'

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β), OrdinalCardinalRamsey3 α β' c') →
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β), OrdinalCardinalRamsey3 α β' c') →
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β), OrdinalCardinalRamsey3 α β' c') →
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β), OrdinalCardinalRamsey3 α β' c') →
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β), OrdinalCardinalRamsey3 α β' c') →
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β), OrdinalCardinalRamsey3 α β' c') →
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β), OrdinalCardinalRamsey3 α β' c') →
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) :
    (c' ≤ c) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) :
    (c' ≤ c) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) :
    (c' ≤ c) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) :
    (c' ≤ c) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) :
    (c' ≤ c) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) :
    (c' ≤ c) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) :
    (c' ≤ c) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c'

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' < c), OrdinalCardinalRamsey3 α β' c'

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') →
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' < c), OrdinalCardinalRamsey3 α β' c') := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') →
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' < c), OrdinalCardinalRamsey3 α β' c') := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') →
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' < c), OrdinalCardinalRamsey3 α β' c') := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') →
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' < c), OrdinalCardinalRamsey3 α β' c') := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') →
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' < c), OrdinalCardinalRamsey3 α β' c') := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') →
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' < c), OrdinalCardinalRamsey3 α β' c') := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') →
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' < c), OrdinalCardinalRamsey3 α β' c') := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) :
    (c' ≤ c) ↔ (c' < c) := by
  omega

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) :
    (c' ≤ c) ↔ (c' < c) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) :
    (c' ≤ c) ↔ (c' < c) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) :
    (c' ≤ c) ↔ (c' < c) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) :
    (c' ≤ c) ↔ (c' < c) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) :
    (c' ≤ c) ↔ (c' < c) := by
  simp_all

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) :
    (c' ≤ c) ↔ (c' < c) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c'

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β ≥ β') (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c'

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} :
    (β' ≤ β) ↔ (β ≥ β') := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} :
    (β' ≤ β) ↔ (β ≥ β') := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} :
    (β' ≤ β) ↔ (β ≥ β') := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} :
    (β' ≤ β) ↔ (β ≥ β') := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} :
    (β' ≤ β) ↔ (β ≥ β') := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} :
    (β' ≤ β) ↔ (β ≥ β') := by
  omega

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} :
    (β' ≤ β) ↔ (β ≥ β') := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} :
    (β' ≤ β) ↔ (β ≥ β') := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') ↔
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β ≥ β') (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') ↔
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β ≥ β') (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') ↔
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β ≥ β') (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') ↔
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β ≥ β') (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c'

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (hβ : β' ≤ β) (h : OrdinalCardinalRamsey3 α β c) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c'

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') ↔
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (hβ : β' ≤ β) (h : OrdinalCardinalRamsey3 α β c) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') ↔
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (hβ : β' ≤ β) (h : OrdinalCardinalRamsey3 α β c) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') ↔
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (hβ : β' ≤ β) (h : OrdinalCardinalRamsey3 α β c) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') ↔
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (hβ : β' ≤ β) (h : OrdinalCardinalRamsey3 α β c) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c'

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h₀ : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c'

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') ↔
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h₀ : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') ↔
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h₀ : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') ↔
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h₀ : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') ↔
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h₀ : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c'

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β ≥ β') (hc : c' < c), OrdinalCardinalRamsey3 α β' c'

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') →
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β ≥ β') (hc : c' < c), OrdinalCardinalRamsey3 α β' c') := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') →
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β ≥ β') (hc : c' < c), OrdinalCardinalRamsey3 α β' c') := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') →
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β ≥ β') (hc : c' < c), OrdinalCardinalRamsey3 α β' c') := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') →
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β ≥ β') (hc : c' < c), OrdinalCardinalRamsey3 α β' c') := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') →
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β ≥ β') (hc : c' < c), OrdinalCardinalRamsey3 α β' c') := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') →
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β ≥ β') (hc : c' < c), OrdinalCardinalRamsey3 α β' c') := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') →
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β ≥ β') (hc : c' < c), OrdinalCardinalRamsey3 α β' c') := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) :
    (c' ≤ c) ↔ (c' < c) := by
  omega

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) :
    (c' ≤ c) ↔ (c' < c) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) :
    (c' ≤ c) ↔ (c' < c) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) :
    (c' ≤ c) ↔ (c' < c) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) :
    (c' ≤ c) ↔ (c' < c) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) :
    (c' ≤ c) ↔ (c' < c) := by
  simp_all

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) :
    (c' ≤ c) ↔ (c' < c) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c'

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β ≥ β'), OrdinalCardinalRamsey3 α β' c'

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β ≥ β'), OrdinalCardinalRamsey3 α β' c') →
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β ≥ β'), OrdinalCardinalRamsey3 α β' c') →
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β ≥ β'), OrdinalCardinalRamsey3 α β' c') →
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β ≥ β'), OrdinalCardinalRamsey3 α β' c') →
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β ≥ β'), OrdinalCardinalRamsey3 α β' c') →
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β ≥ β'), OrdinalCardinalRamsey3 α β' c') →
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β ≥ β'), OrdinalCardinalRamsey3 α β' c') →
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) :
    (c' ≤ c) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) :
    (c' ≤ c) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) :
    (c' ≤ c) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) :
    (c' ≤ c) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) :
    (c' ≤ c) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) :
    (c' ≤ c) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) :
    (c' ≤ c) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c'

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (hβ : β' ≤ β) (h : OrdinalCardinalRamsey3 α β c), OrdinalCardinalRamsey3 α β' c'

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (hβ : β' ≤ β) (h : OrdinalCardinalRamsey3 α β c), OrdinalCardinalRamsey3 α β' c') →
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (hβ : β' ≤ β) (h : OrdinalCardinalRamsey3 α β c), OrdinalCardinalRamsey3 α β' c') →
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (hβ : β' ≤ β) (h : OrdinalCardinalRamsey3 α β c), OrdinalCardinalRamsey3 α β' c') →
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (hβ : β' ≤ β) (h : OrdinalCardinalRamsey3 α β c), OrdinalCardinalRamsey3 α β' c') →
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (hβ : β' ≤ β) (h : OrdinalCardinalRamsey3 α β c), OrdinalCardinalRamsey3 α β' c') →
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (hβ : β' ≤ β) (h : OrdinalCardinalRamsey3 α β c), OrdinalCardinalRamsey3 α β' c') →
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (hβ : β' ≤ β) (h : OrdinalCardinalRamsey3 α β c), OrdinalCardinalRamsey3 α β' c') →
    (∀ {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c), OrdinalCardinalRamsey3 α β' c') := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) :
    (c' ≤ c) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) :
    (c' ≤ c) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) :
    (c' ≤ c) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) :
    (c' ≤ c) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) :
    (c' ≤ c) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) :
    (c' ≤ c) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) :
    (c' ≤ c) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}} (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
