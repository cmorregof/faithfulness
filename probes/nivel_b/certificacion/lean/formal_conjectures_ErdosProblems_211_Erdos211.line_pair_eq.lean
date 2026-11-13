import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Geometry.2d
--   notación `ℝ²` (scoped EuclideanGeometry, FCM.Geometry.2d)
/-!
# Erdős Problem 211

*References:*
- [erdosproblems.com/211](https://www.erdosproblems.com/211)
- [Be83] Beck, József, *On the lattice property of the plane and some problems of Dirac,
  Motzkin and Erdős in combinatorial geometry*. Combinatorica (1983), 281-297.
- [SzTr83] Szemerédi, Endre and Trotter, Jr., William T., *Extremal problems in discrete
  geometry*. Combinatorica (1983), 381-392.
- [Er84] Erdős, P., *Research problems*. Period. Math. Hungar. (1984), 101-103.
- [BGS74] Burr, Stefan A. and Grünbaum, Branko and Sloane, N. J. A., *The orchard problem*.
  Geometriae Dedicata (1974), 397-424.
- [FuPa84] Füredi, Z. and Palásti, I., *Arrangements of lines with a large number of triangles*.
  Proc. Amer. Math. Soc. (1984), 561-566.
-/

section

namespace Erdos211

open EuclideanGeometry Filter

open scoped Classical in
/-- Distinct lines containing two distinct points of the configuration. -/
noncomputable def determinedLines (s : Finset ℝ²) : Finset (AffineSubspace ℝ ℝ²) :=
  s.offDiag.image fun p => line[ℝ, p.1, p.2]

open scoped Classical in
/-- The uniform Erdős–Beck lower bound. -/
def MainBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (n k : ℕ), 1 ≤ k → k < n →
    ∀ s : Finset ℝ², s.card = n →
      (∀ L : AffineSubspace ℝ ℝ², IsLine L → (s.filter fun p => p ∈ L).card ≤ n - k) →
      c * (k : ℝ) * (n : ℝ) ≤ ((determinedLines s).card : ℝ)

open scoped Classical in
/-- The quadratic lower bound for configurations with at most half the points on a line. -/
def QuadraticBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
    ∀ s : Finset ℝ², s.card = 2 * n →
      (∀ L : AffineSubspace ℝ ℝ², IsLine L → (s.filter fun p => p ∈ L).card ≤ n) →
      c * (n : ℝ) ^ 2 ≤ ((determinedLines s).card : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b), line[ℝ, a, b] = L

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L), line[ℝ, a, b] = L

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L), line[ℝ, a, b] = L) →
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b), line[ℝ, a, b] = L) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L), line[ℝ, a, b] = L) →
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b), line[ℝ, a, b] = L) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L), line[ℝ, a, b] = L) →
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b), line[ℝ, a, b] = L) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L), line[ℝ, a, b] = L) →
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b), line[ℝ, a, b] = L) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L), line[ℝ, a, b] = L) →
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b), line[ℝ, a, b] = L) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L), line[ℝ, a, b] = L) →
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b), line[ℝ, a, b] = L) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L), line[ℝ, a, b] = L) →
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b), line[ℝ, a, b] = L) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) :
    (a ≠ b) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) :
    (a ≠ b) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) :
    (a ≠ b) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) :
    (a ≠ b) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) :
    (a ≠ b) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) :
    (a ≠ b) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) :
    (a ≠ b) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b), line[ℝ, a, b] = L

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : ¬(a = b)), line[ℝ, a, b] = L

set_option maxHeartbeats 200000 in
example {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} :
    (a ≠ b) ↔ (¬(a = b)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} :
    (a ≠ b) ↔ (¬(a = b)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} :
    (a ≠ b) ↔ (¬(a = b)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} :
    (a ≠ b) ↔ (¬(a = b)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} :
    (a ≠ b) ↔ (¬(a = b)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} :
    (a ≠ b) ↔ (¬(a = b)) := by
  omega

set_option maxHeartbeats 200000 in
example {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} :
    (a ≠ b) ↔ (¬(a = b)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} :
    (a ≠ b) ↔ (¬(a = b)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b), line[ℝ, a, b] = L) ↔
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : ¬(a = b)), line[ℝ, a, b] = L) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b), line[ℝ, a, b] = L) ↔
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : ¬(a = b)), line[ℝ, a, b] = L) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b), line[ℝ, a, b] = L) ↔
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : ¬(a = b)), line[ℝ, a, b] = L) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b), line[ℝ, a, b] = L) ↔
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : ¬(a = b)), line[ℝ, a, b] = L) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b), line[ℝ, a, b] = L

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (ha : a ∈ L) (hL : IsLine L) (hb : b ∈ L) (hab : a ≠ b), line[ℝ, a, b] = L

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b), line[ℝ, a, b] = L) ↔
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (ha : a ∈ L) (hL : IsLine L) (hb : b ∈ L) (hab : a ≠ b), line[ℝ, a, b] = L) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b), line[ℝ, a, b] = L) ↔
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (ha : a ∈ L) (hL : IsLine L) (hb : b ∈ L) (hab : a ≠ b), line[ℝ, a, b] = L) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b), line[ℝ, a, b] = L) ↔
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (ha : a ∈ L) (hL : IsLine L) (hb : b ∈ L) (hab : a ≠ b), line[ℝ, a, b] = L) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b), line[ℝ, a, b] = L) ↔
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (ha : a ∈ L) (hL : IsLine L) (hb : b ∈ L) (hab : a ≠ b), line[ℝ, a, b] = L) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b), line[ℝ, a, b] = L

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL₀ : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b), line[ℝ, a, b] = L

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b), line[ℝ, a, b] = L) ↔
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL₀ : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b), line[ℝ, a, b] = L) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b), line[ℝ, a, b] = L) ↔
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL₀ : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b), line[ℝ, a, b] = L) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b), line[ℝ, a, b] = L) ↔
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL₀ : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b), line[ℝ, a, b] = L) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b), line[ℝ, a, b] = L) ↔
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL₀ : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b), line[ℝ, a, b] = L) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b), line[ℝ, a, b] = L

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (ha : a ∈ L) (hL : IsLine L) (hb : b ∈ L), line[ℝ, a, b] = L

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (ha : a ∈ L) (hL : IsLine L) (hb : b ∈ L), line[ℝ, a, b] = L) →
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b), line[ℝ, a, b] = L) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (ha : a ∈ L) (hL : IsLine L) (hb : b ∈ L), line[ℝ, a, b] = L) →
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b), line[ℝ, a, b] = L) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (ha : a ∈ L) (hL : IsLine L) (hb : b ∈ L), line[ℝ, a, b] = L) →
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b), line[ℝ, a, b] = L) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (ha : a ∈ L) (hL : IsLine L) (hb : b ∈ L), line[ℝ, a, b] = L) →
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b), line[ℝ, a, b] = L) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (ha : a ∈ L) (hL : IsLine L) (hb : b ∈ L), line[ℝ, a, b] = L) →
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b), line[ℝ, a, b] = L) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (ha : a ∈ L) (hL : IsLine L) (hb : b ∈ L), line[ℝ, a, b] = L) →
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b), line[ℝ, a, b] = L) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (ha : a ∈ L) (hL : IsLine L) (hb : b ∈ L), line[ℝ, a, b] = L) →
    (∀ {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b), line[ℝ, a, b] = L) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) :
    (a ≠ b) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) :
    (a ≠ b) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) :
    (a ≠ b) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) :
    (a ≠ b) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) :
    (a ≠ b) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) :
    (a ≠ b) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) :
    (a ≠ b) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {a b : ℝ²} {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
