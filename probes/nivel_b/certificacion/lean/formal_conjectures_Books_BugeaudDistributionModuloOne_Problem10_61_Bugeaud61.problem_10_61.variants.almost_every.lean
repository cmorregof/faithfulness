import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Analysis.Equidistribution.ModOne
/-!
# Bugeaud Collection of Conjectures and Open Questions: Pisot orbits on the Cantor set

Problem 10.61, proposed by Mendès France [MF67, Problème 1, p. 41]. For a Pisot number
$\alpha > 2$ put
$$C(\alpha) = \left\{ (\alpha - 1) \sum_{k \ge 1} \varepsilon_k \alpha^{-k} :
\varepsilon_k \in \{0, 1\} \right\}.$$
The problem asks to prove that $(\xi \alpha^n)_{n \ge 1}$ is not uniformly distributed
modulo one for any $\xi \in C(\alpha)$. In the language of [MF67] this reads
$C(\alpha) \cap B(\alpha) = \emptyset$, where $B(\alpha)$ is the set of $\xi$ for which
$(\xi \alpha^n)$ is uniformly distributed modulo one.

The problem is open. It is easy for an integer base and settled for two quadratic
$\alpha$; the general Pisot case is what remains. [Ste26] reduces it to a statement about
shift-invariant measures of the full two-shift, and proves that every true instance admits
a finite certificate, so the difficulty is uniformity in $\alpha$ rather than any single
$\alpha$. The variants below state the criterion and the instances of [Ste26] that concern
Problem 10.61 directly; the reduction itself is not stated here, since it needs the symbolic
model.

Deleting the term $n = 0$ does not change uniform distribution modulo one, so the
statements indexed from $n = 1$ agree with the ones of [Ste26], which are indexed from
$n = 0$. Where an orbit is confined away from an interval the stronger form, for every
$n \ge 0$, is stated.

*References:*
  - [Bug12] Bugeaud, Yann. "Distribution modulo one and Diophantine approximation."
    Vol. 193. Cambridge University Press, 2012. Chapter 10, Problem 10.61, p. 222.
  - [MF67] Mendès France, Michel. "Nombres normaux. Applications aux fonctions
    pseudo-aléatoires." Journal d'Analyse Mathématique 20 (1967): 1-56.
  - [Kok35] Koksma, Jurjen F. "Ein mengentheoretischer Satz über die Gleichverteilung
    modulo Eins." Compositio Mathematica 2 (1935): 250-258.
  - [Ste26] Stephan, Ralf. "Criteria for the non-equidistribution of $(\xi \alpha^n)$ on
    the Cantor set $C(\alpha)$." Preprint, 2026.
    https://doi.org/10.13140/RG.2.2.13923.52001
-/

section

namespace Bugeaud61

/--
The point of $C(\alpha)$ with digit sequence $\varepsilon$, that is
$(\alpha - 1) \sum_{k \ge 1} \varepsilon_k \alpha^{-k}$.
-/
noncomputable def cantorPoint (α : ℝ) (ε : ℕ → Bool) : ℝ :=
  (α - 1) * ∑' k : ℕ, (if ε k then (1 : ℝ) else 0) * α⁻¹ ^ (k + 1)

/--
The set $C(\alpha)$ of Problem 10.61. For $\alpha > 2$ it is a Cantor set of Hausdorff
dimension $\log 2 / \log \alpha < 1$, normalised so that $0$ is its least and $1$ its
greatest element.
-/
noncomputable def pisotCantorSet (α : ℝ) : Set ℝ := Set.range (cantorPoint α)

/--
The Route A exponent $A(\alpha) = \log 2 / \log \alpha + \log 2 / \log(1 / \rho)$ of
[Ste26], where $\rho$ is the largest modulus of a conjugate of $\alpha$ other than
$\alpha$ itself. It is the sum of the box dimensions of $C(\alpha)$ and of the window in
which the conjugate contributions live.
-/
noncomputable def routeAExponent (α ρ : ℝ) : ℝ :=
  Real.log 2 / Real.log α + Real.log 2 / Real.log ρ⁻¹

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : 1 < α), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : 1 ≤ α), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 1 ≤ α), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) →
    (∀ (α : ℝ) (hα : 1 < α), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 1 ≤ α), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) →
    (∀ (α : ℝ) (hα : 1 < α), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 1 ≤ α), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) →
    (∀ (α : ℝ) (hα : 1 < α), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 1 ≤ α), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) →
    (∀ (α : ℝ) (hα : 1 < α), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 1 ≤ α), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) →
    (∀ (α : ℝ) (hα : 1 < α), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 1 ≤ α), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) →
    (∀ (α : ℝ) (hα : 1 < α), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 1 ≤ α), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) →
    (∀ (α : ℝ) (hα : 1 < α), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (α : ℝ)  :
    (1 < α) ↔ (1 ≤ α) := by
  omega

set_option maxHeartbeats 200000 in
example (α : ℝ)  :
    (1 < α) ↔ (1 ≤ α) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (α : ℝ)  :
    (1 < α) ↔ (1 ≤ α) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (α : ℝ)  :
    (1 < α) ↔ (1 ≤ α) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (α : ℝ)  :
    (1 < α) ↔ (1 ≤ α) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (α : ℝ)  :
    (1 < α) ↔ (1 ≤ α) := by
  simp_all

set_option maxHeartbeats 200000 in
example (α : ℝ)  :
    (1 < α) ↔ (1 ≤ α) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (¬((1 < α) ↔ (1 ≤ α))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (¬((1 < α) ↔ (1 ≤ α))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (¬((1 < α) ↔ (1 ≤ α))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (¬((1 < α) ↔ (1 ≤ α))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (¬((1 < α) ↔ (1 ≤ α))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (¬((1 < α) ↔ (1 ≤ α))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((1 < α) ↔ (1 ≤ α)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((1 < α) ↔ (1 ≤ α)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((1 < α) ↔ (1 ≤ α)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((1 < α) ↔ (1 ≤ α)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((1 < α) ↔ (1 ≤ α)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((1 < α) ↔ (1 ≤ α)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : 1 < α), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : α > 1), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (1 < α) ↔ (α > 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (1 < α) ↔ (α > 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (1 < α) ↔ (α > 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (1 < α) ↔ (α > 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (1 < α) ↔ (α > 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (1 < α) ↔ (α > 1) := by
  omega

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (1 < α) ↔ (α > 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (1 < α) ↔ (α > 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 1 < α), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) ↔
    (∀ (α : ℝ) (hα : α > 1), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 1 < α), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) ↔
    (∀ (α : ℝ) (hα : α > 1), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 1 < α), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) ↔
    (∀ (α : ℝ) (hα : α > 1), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 1 < α), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) ↔
    (∀ (α : ℝ) (hα : α > 1), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : 1 < α), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα₀ : 1 < α), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 1 < α), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) ↔
    (∀ (α : ℝ) (hα₀ : 1 < α), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 1 < α), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) ↔
    (∀ (α : ℝ) (hα₀ : 1 < α), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 1 < α), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) ↔
    (∀ (α : ℝ) (hα₀ : 1 < α), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 1 < α), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) ↔
    (∀ (α : ℝ) (hα₀ : 1 < α), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : 1 < α), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : ¬(α ≤ 1)), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (1 < α) ↔ (¬(α ≤ 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (1 < α) ↔ (¬(α ≤ 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (1 < α) ↔ (¬(α ≤ 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (1 < α) ↔ (¬(α ≤ 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (1 < α) ↔ (¬(α ≤ 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (1 < α) ↔ (¬(α ≤ 1)) := by
  omega

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (1 < α) ↔ (¬(α ≤ 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (1 < α) ↔ (¬(α ≤ 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 1 < α), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) ↔
    (∀ (α : ℝ) (hα : ¬(α ≤ 1)), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 1 < α), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) ↔
    (∀ (α : ℝ) (hα : ¬(α ≤ 1)), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 1 < α), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) ↔
    (∀ (α : ℝ) (hα : ¬(α ≤ 1)), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : 1 < α), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) ↔
    (∀ (α : ℝ) (hα : ¬(α ≤ 1)), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : 1 < α), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : α ≥ 1), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : α ≥ 1), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) →
    (∀ (α : ℝ) (hα : 1 < α), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : α ≥ 1), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) →
    (∀ (α : ℝ) (hα : 1 < α), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : α ≥ 1), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) →
    (∀ (α : ℝ) (hα : 1 < α), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : α ≥ 1), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) →
    (∀ (α : ℝ) (hα : 1 < α), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : α ≥ 1), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) →
    (∀ (α : ℝ) (hα : 1 < α), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : α ≥ 1), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) →
    (∀ (α : ℝ) (hα : 1 < α), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : α ≥ 1), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) →
    (∀ (α : ℝ) (hα : 1 < α), ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (α : ℝ)  :
    (1 < α) ↔ (α ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example (α : ℝ)  :
    (1 < α) ↔ (α ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (α : ℝ)  :
    (1 < α) ↔ (α ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (α : ℝ)  :
    (1 < α) ↔ (α ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (α : ℝ)  :
    (1 < α) ↔ (α ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (α : ℝ)  :
    (1 < α) ↔ (α ≥ 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example (α : ℝ)  :
    (1 < α) ↔ (α ≥ 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (¬((1 < α) ↔ (α ≥ 1))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (¬((1 < α) ↔ (α ≥ 1))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (¬((1 < α) ↔ (α ≥ 1))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (¬((1 < α) ↔ (α ≥ 1))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (¬((1 < α) ↔ (α ≥ 1))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (¬((1 < α) ↔ (α ≥ 1))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((1 < α) ↔ (α ≥ 1)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((1 < α) ↔ (α ≥ 1)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((1 < α) ↔ (α ≥ 1)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((1 < α) ↔ (α ≥ 1)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((1 < α) ↔ (α ≥ 1)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((1 < α) ↔ (α ≥ 1)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα : 1 < α) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα : 1 < α) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα : 1 < α) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα : 1 < α) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα : 1 < α) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
