import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Some conjectures about ranks of elliptic curves over ℚ

*References:*
- [PPVW2016] Jennifer Park, Bjorn Poonen, John Voight, and Melanie Matchett Wood.
    A heuristic for boundedness of ranks of elliptic curves,
    https://ems.press/journals/jems/articles/16228
- [BS2013] Manjul Bhargava and Arul Shankar. The average size of the 5-Selmer group of
   elliptic curves is 6, and the average rank is less than 1, https://arxiv.org/pdf/1312.7859
- [Goldfeld1979] Dorian Goldfeld. Conjectures on elliptic curves over quadratic fields,
   Number Theory Carbondale 1979, Lecture Notes in Math. 751, 108-118,
   https://doi.org/10.1007/BFb0062705
- [Smith2025] Alexander Smith. The Birch and Swinnerton-Dyer conjecture implies Goldfeld's
   conjecture, https://arxiv.org/abs/2503.17619
- [Wikipedia](https://en.wikipedia.org/wiki/Rank_of_an_elliptic_curve)
- [ICARM](https://elliptic-rank.icarm.cloud/curve/273)
- [Stoll] Michael Stoll. EllipticCurves, a Lean 4 formalization of the Mordell–Weil theorem
   and explicit 2-descent, https://github.com/MichaelStollBayreuth/EllipticCurves
-/

section

namespace EllipticCurveRank

open EllipticCurveRank

/-- A data structure representing isomoprhism classes of elliptic curves over ℚ.
Every elliptic curve over ℚ is isomorphic to one with Weierstrass equation `y² = x³ + Ax + B`,
and the pair `(A,B)` is unique if it satisfy the `reduced` condition below.
See Section 5.1 in [PPVW2016]. -/
structure RatEllipticCurve : Type where
  A : ℤ
  B : ℤ
  reduced (p : ℕ) : p.Prime → ¬ ((p ^ 4 : ℤ) ∣ A ∧ (p ^ 6 : ℤ) ∣ B)
  Δ_ne_zero : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0

open Module (finrank)
open WeierstrassCurve

namespace RatEllipticCurve

/-- Convert the structure `RatEllipticCurve` to a Weierstrass curve. -/
def toWeierstrass (E : RatEllipticCurve) : Affine ℚ :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := E.A, a₆ := E.B }

/-- The rank of an elliptic curve over ℚ. -/
noncomputable abbrev rank (E : RatEllipticCurve) : ℕ := finrank ℤ E.toWeierstrass.Point

open WeierstrassCurve in
instance (E : RatEllipticCurve) : E.toWeierstrass.IsElliptic where
  isUnit := isUnit_iff_ne_zero.mpr <| by
    convert mul_ne_zero (show (-16 : ℚ) ≠ 0 by norm_num) (Int.cast_ne_zero.mpr E.Δ_ne_zero)
    simp_rw [toWeierstrass, Δ, b₂, b₄, b₆, Int.cast_add, Int.cast_mul, Int.cast_pow]
    ring

/-- The naïve height of an elliptic curve over ℚ. -/
def naiveHeight (E : RatEllipticCurve) : ℕ := max (4 * E.A.natAbs ^ 3) (27 * E.B.natAbs ^ 2)

/-- The set of elliptic curves over ℚ with naïve height less than or equal to a given height. -/
def heightLE (H : ℕ) : Set RatEllipticCurve := {E : RatEllipticCurve | E.naiveHeight ≤ H}

open scoped Topology
open Filter (atTop)

/-- The quadratic twist $E^d$ of $E : y^2 = x^3 + Ax + B$ by an integer $d$, given by the
Weierstrass equation $y^2 = x^3 + d^2Ax + d^3B$. For $d \neq 0$ this is the twist of $E$
corresponding to the quadratic field $\mathbb{Q}(\sqrt{d})$. See Section 1 of [Smith2025]. -/
def quadraticTwist (E : RatEllipticCurve) (d : ℤ) : Affine ℚ :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := d ^ 2 * E.A, a₆ := d ^ 3 * E.B }

/-- The rank of the quadratic twist $E^d$ of an elliptic curve $E$ over $\mathbb{Q}$. -/
noncomputable abbrev twistRank (E : RatEllipticCurve) (d : ℤ) : ℕ :=
  finrank ℤ (E.quadraticTwist d).Point

/-- The set of nonzero integers $d$ with $|d| \leq H$, which index the quadratic twists $E^d$
ordered by $|d|$. By `naiveHeight_quadraticTwist` this is the same as ordering them by height. -/
def twistIndexLE (H : ℕ) : Set ℤ := {d : ℤ | d ≠ 0 ∧ |d| ≤ (H : ℤ)}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (E : RatEllipticCurve) (r : ℕ), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) →
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) →
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) →
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) →
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) →
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) →
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) →
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ)  :
    (2 ≤ r) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ)  :
    (2 ≤ r) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ)  :
    (2 ≤ r) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ)  :
    (2 ≤ r) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ)  :
    (2 ≤ r) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ)  :
    (2 ≤ r) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ)  :
    (2 ≤ r) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((2 ≤ r) ↔ (True))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((2 ≤ r) ↔ (True))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((2 ≤ r) ↔ (True))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((2 ≤ r) ↔ (True))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((2 ≤ r) ↔ (True))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((2 ≤ r) ↔ (True))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 < r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) →
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 < r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) →
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 < r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) →
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 < r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) →
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 < r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) →
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 < r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) →
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 < r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) →
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 < r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ)  :
    (2 ≤ r) ↔ (2 < r) := by
  omega

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ)  :
    (2 ≤ r) ↔ (2 < r) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ)  :
    (2 ≤ r) ↔ (2 < r) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ)  :
    (2 ≤ r) ↔ (2 < r) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ)  :
    (2 ≤ r) ↔ (2 < r) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ)  :
    (2 ≤ r) ↔ (2 < r) := by
  simp_all

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ)  :
    (2 ≤ r) ↔ (2 < r) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((2 ≤ r) ↔ (2 < r))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((2 ≤ r) ↔ (2 < r))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((2 ≤ r) ↔ (2 < r))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((2 ≤ r) ↔ (2 < r))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((2 ≤ r) ↔ (2 < r))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((2 ≤ r) ↔ (2 < r))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (2 < r)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (2 < r)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (2 < r)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (2 < r)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (2 < r)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (2 < r)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (E : RatEllipticCurve) (r : ℕ) (hr : 3 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) →
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 3 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) →
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 3 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) →
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 3 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) →
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 3 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) →
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 3 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) →
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 3 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) →
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 3 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ)  :
    (2 ≤ r) ↔ (3 ≤ r) := by
  omega

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ)  :
    (2 ≤ r) ↔ (3 ≤ r) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ)  :
    (2 ≤ r) ↔ (3 ≤ r) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ)  :
    (2 ≤ r) ↔ (3 ≤ r) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ)  :
    (2 ≤ r) ↔ (3 ≤ r) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ)  :
    (2 ≤ r) ↔ (3 ≤ r) := by
  simp_all

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ)  :
    (2 ≤ r) ↔ (3 ≤ r) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((2 ≤ r) ↔ (3 ≤ r))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((2 ≤ r) ↔ (3 ≤ r))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((2 ≤ r) ↔ (3 ≤ r))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((2 ≤ r) ↔ (3 ≤ r))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((2 ≤ r) ↔ (3 ≤ r))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((2 ≤ r) ↔ (3 ≤ r))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((2 ≤ r) ↔ (3 ≤ r))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (3 ≤ r)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (3 ≤ r)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (3 ≤ r)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (3 ≤ r)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (3 ≤ r)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (3 ≤ r)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (3 ≤ r)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (E : RatEllipticCurve) (r : ℕ) (hr : r ≥ 2), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ) :
    (2 ≤ r) ↔ (r ≥ 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ) :
    (2 ≤ r) ↔ (r ≥ 2) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ) :
    (2 ≤ r) ↔ (r ≥ 2) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ) :
    (2 ≤ r) ↔ (r ≥ 2) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ) :
    (2 ≤ r) ↔ (r ≥ 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ) :
    (2 ≤ r) ↔ (r ≥ 2) := by
  omega

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ) :
    (2 ≤ r) ↔ (r ≥ 2) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ) :
    (2 ≤ r) ↔ (r ≥ 2) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) ↔
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : r ≥ 2), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) ↔
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : r ≥ 2), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) ↔
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : r ≥ 2), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) ↔
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : r ≥ 2), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (E : RatEllipticCurve) (r : ℕ) (hr₀ : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) ↔
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr₀ : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) ↔
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr₀ : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) ↔
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr₀ : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) ↔
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr₀ : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (E : RatEllipticCurve) (r : ℕ) (hr : ¬(r < 2)), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ) :
    (2 ≤ r) ↔ (¬(r < 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ) :
    (2 ≤ r) ↔ (¬(r < 2)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ) :
    (2 ≤ r) ↔ (¬(r < 2)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ) :
    (2 ≤ r) ↔ (¬(r < 2)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ) :
    (2 ≤ r) ↔ (¬(r < 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ) :
    (2 ≤ r) ↔ (¬(r < 2)) := by
  omega

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ) :
    (2 ≤ r) ↔ (¬(r < 2)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ) :
    (2 ≤ r) ↔ (¬(r < 2)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) ↔
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : ¬(r < 2)), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) ↔
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : ¬(r < 2)), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) ↔
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : ¬(r < 2)), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) ↔
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : ¬(r < 2)), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (E : RatEllipticCurve) (r : ℕ) (hr : 1 < r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ) :
    (2 ≤ r) ↔ (1 < r) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ) :
    (2 ≤ r) ↔ (1 < r) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ) :
    (2 ≤ r) ↔ (1 < r) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ) :
    (2 ≤ r) ↔ (1 < r) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ) :
    (2 ≤ r) ↔ (1 < r) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ) :
    (2 ≤ r) ↔ (1 < r) := by
  omega

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ) :
    (2 ≤ r) ↔ (1 < r) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ) :
    (2 ≤ r) ↔ (1 < r) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) ↔
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 1 < r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) ↔
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 1 < r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) ↔
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 1 < r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) ↔
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 1 < r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (E : RatEllipticCurve) (r : ℕ) (hr : r > 2), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) →
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : r > 2), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) →
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : r > 2), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) →
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : r > 2), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) →
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : r > 2), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) →
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : r > 2), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) →
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : r > 2), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) →
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : r > 2), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ)  :
    (2 ≤ r) ↔ (r > 2) := by
  omega

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ)  :
    (2 ≤ r) ↔ (r > 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ)  :
    (2 ≤ r) ↔ (r > 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ)  :
    (2 ≤ r) ↔ (r > 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ)  :
    (2 ≤ r) ↔ (r > 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ)  :
    (2 ≤ r) ↔ (r > 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ)  :
    (2 ≤ r) ↔ (r > 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((2 ≤ r) ↔ (r > 2))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((2 ≤ r) ↔ (r > 2))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((2 ≤ r) ↔ (r > 2))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((2 ≤ r) ↔ (r > 2))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((2 ≤ r) ↔ (r > 2))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((2 ≤ r) ↔ (r > 2))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (r > 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (r > 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (r > 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (r > 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (r > 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (r > 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (E : RatEllipticCurve) (r : ℕ) (hr : r ≥ 3), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) →
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : r ≥ 3), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) →
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : r ≥ 3), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) →
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : r ≥ 3), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) →
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : r ≥ 3), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) →
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : r ≥ 3), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) →
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : r ≥ 3), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) →
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : r ≥ 3), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ)  :
    (2 ≤ r) ↔ (r ≥ 3) := by
  omega

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ)  :
    (2 ≤ r) ↔ (r ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ)  :
    (2 ≤ r) ↔ (r ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ)  :
    (2 ≤ r) ↔ (r ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ)  :
    (2 ≤ r) ↔ (r ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ)  :
    (2 ≤ r) ↔ (r ≥ 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ)  :
    (2 ≤ r) ↔ (r ≥ 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((2 ≤ r) ↔ (r ≥ 3))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((2 ≤ r) ↔ (r ≥ 3))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((2 ≤ r) ↔ (r ≥ 3))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((2 ≤ r) ↔ (r ≥ 3))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((2 ≤ r) ↔ (r ≥ 3))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((2 ≤ r) ↔ (r ≥ 3))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((2 ≤ r) ↔ (r ≥ 3))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (r ≥ 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (r ≥ 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (r ≥ 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (r ≥ 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (r ≥ 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (r ≥ 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (r ≥ 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (E : RatEllipticCurve) (r : ℕ) (hr : 1 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 1 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) →
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 1 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) →
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 1 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) →
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 1 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) →
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 1 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) →
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 1 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) →
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 1 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) →
    (∀ (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r), atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ)  :
    (2 ≤ r) ↔ (1 ≤ r) := by
  omega

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ)  :
    (2 ≤ r) ↔ (1 ≤ r) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ)  :
    (2 ≤ r) ↔ (1 ≤ r) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ)  :
    (2 ≤ r) ↔ (1 ≤ r) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ)  :
    (2 ≤ r) ↔ (1 ≤ r) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ)  :
    (2 ≤ r) ↔ (1 ≤ r) := by
  simp_all

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ)  :
    (2 ≤ r) ↔ (1 ≤ r) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((2 ≤ r) ↔ (1 ≤ r))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((2 ≤ r) ↔ (1 ≤ r))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((2 ≤ r) ↔ (1 ≤ r))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((2 ≤ r) ↔ (1 ≤ r))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((2 ≤ r) ↔ (1 ≤ r))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((2 ≤ r) ↔ (1 ≤ r))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (1 ≤ r)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (1 ≤ r)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (1 ≤ r)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (1 ≤ r)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (1 ≤ r)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (1 ≤ r)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
