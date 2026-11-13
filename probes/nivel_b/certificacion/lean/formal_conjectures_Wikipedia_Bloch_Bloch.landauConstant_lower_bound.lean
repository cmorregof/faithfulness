import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Bloch and Landau constants

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Bloch%27s_theorem_(complex_analysis))
- [CP96] Chen, H., Gauthier, P. M. "On Bloch's constant." Journal d'Analyse Mathématique 69 (1996),
  275–291.
- [AG37] Ahlfors, L. V., Grunsky, H. "Über die Blochsche Konstante." Mathematische Zeitschrift 42
  (1937), 671–673.
- [Ya95] Yanagihara, H. "On the locally univalent Bloch constant." Journal d'Analyse Mathématique
  65 (1995), 1–17.
- [Ra43] Rademacher, H. "On the Bloch-Landau Constant."" American Journal of Mathematics 65 (1943),
  387–390.
- [OptimizationConstants](https://teorth.github.io/optimizationproblems/constants/57c.html)
- [Skin2009] Skinner, Brian. The univalent Bloch constant problem. Complex Variables and Elliptic
  Equations 54 (2009), no. 10, 951–955.
- [MathWorld](https://mathworld.wolfram.com/BlochConstant.html)
- [Bhowmik–Sen](https://www.cambridge.org/core/journals/canadian-mathematical-bulletin/article/improved-bloch-and-landau-constants-for-meromorphic-functions/FD465D1F2CEF7E8C62AFF16C3E89B7B4)
- [Re2008] Rettinger, R. ["Bloch's constant is computable."](https://jucs.org/jucs_14_6/blochs_constant_is_computable/jucs_14_06_0896_0907_rettinger.pdf)
  Journal of Universal Computer Science 14 (2008), 896–907. In particular, a schlicht disk is the
  image of a subdomain under a biholomorphic restriction.
-/

section

open scoped Topology ENNReal
open Metric Set Filter
namespace Bloch

/-- The **Bloch radius** $B_f$ of a function $f$ is the supremum of radii of schlicht disks in the
image of the unit disk under $f$: the restriction of `f` maps an open subdomain injectively and
onto the disk. Requiring an open subdomain and equality of the image is essential; mere containment
would allow an arbitrary set-theoretic choice of one preimage per point. Takes values in `ℝ≥0∞` so
that functions whose image contains arbitrarily large schlicht disks correctly get radius `⊤`
rather than `0`. -/
noncomputable def blochRadius (f : ℂ → ℂ) : ℝ≥0∞ :=
  sSup (ENNReal.ofReal '' {r : ℝ | ∃ S, IsOpen S ∧ S ⊆ ball (0 : ℂ) 1 ∧
    ∃ x, f '' S = ball x r ∧ InjOn f S})

/-- The **Landau radius** $L_f$ of a function $f$ is the supremum of radii of disks contained in
the image of the unit disk under $f$. Takes values in `ℝ≥0∞` so that functions with unbounded
image correctly get radius `⊤`. -/
noncomputable def landauRadius (f : ℂ → ℂ) : ℝ≥0∞ :=
  sSup (ENNReal.ofReal '' {r : ℝ | ∃ x, ball x r ⊆ f '' (ball (0 : ℂ) 1)})

/-- The **Bloch constant** $B$ is the largest radius such that every holomorphic function on the
unit disk with $f'(0) = 1$ has a schlicht (univalent) disk of that radius in its image. -/
noncomputable def blochConstant : ℝ :=
  sSup {B : ℝ | ∀ f : ℂ → ℂ, DifferentiableOn ℂ f (ball 0 1) → deriv f 0 = 1 →
    ∃ S, IsOpen S ∧ S ⊆ ball 0 1 ∧ ∃ x, f '' S = ball x B ∧ InjOn f S}

/-- The **Univalent Bloch constant** $B_u$ is the largest radius such that every univalent
holomorphic function on the unit disk with $f'(0) = 1$ has a schlicht disk of that radius in its
image. -/
noncomputable def univalentBlochConstant : ℝ :=
  sSup {B : ℝ | ∀ f : ℂ → ℂ, InjOn f (ball 0 1) → DifferentiableOn ℂ f (ball 0 1) →
    deriv f 0 = 1 → ∃ S, IsOpen S ∧ S ⊆ ball 0 1 ∧
      ∃ x, f '' S = ball x B ∧ InjOn f S}

/-- The **Landau constant** $L$ is the largest radius such that every holomorphic function on the
unit disk with $f'(0) = 1$ has a disk of that radius contained in its image. -/
noncomputable def landauConstant : ℝ :=
  sSup {B : ℝ | ∀ f : ℂ → ℂ, DifferentiableOn ℂ f (ball 0 1) → deriv f 0 = 1 →
    ∃ x, ball x B ⊆ f '' (ball 0 1)}

set_option maxHeartbeats 200000 in
example : Prop :=
  0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant

set_option maxHeartbeats 200000 in
example : Prop :=
  0.5 + 10 ^ (-335 : ℤ) < landauConstant

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) < landauConstant) →
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) < landauConstant) →
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) < landauConstant) →
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) < landauConstant) →
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) < landauConstant) →
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) < landauConstant) →
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) < landauConstant) →
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (¬(0.5 + 10 ^ (-335 : ℤ) < landauConstant)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (¬(0.5 + 10 ^ (-335 : ℤ) < landauConstant)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) ↔ (0.5 + 10 ^ (-335 : ℤ) < landauConstant)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) ↔ (0.5 + 10 ^ (-335 : ℤ) < landauConstant)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant

set_option maxHeartbeats 200000 in
example : Prop :=
  0.5 + 11 ^ (-335 : ℤ) ≤ landauConstant

set_option maxHeartbeats 200000 in
example :
    (0.5 + 11 ^ (-335 : ℤ) ≤ landauConstant) →
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (0.5 + 11 ^ (-335 : ℤ) ≤ landauConstant) →
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (0.5 + 11 ^ (-335 : ℤ) ≤ landauConstant) →
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (0.5 + 11 ^ (-335 : ℤ) ≤ landauConstant) →
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (0.5 + 11 ^ (-335 : ℤ) ≤ landauConstant) →
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (0.5 + 11 ^ (-335 : ℤ) ≤ landauConstant) →
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (0.5 + 11 ^ (-335 : ℤ) ≤ landauConstant) →
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) →
    (0.5 + 11 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) →
    (0.5 + 11 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) →
    (0.5 + 11 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) →
    (0.5 + 11 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) →
    (0.5 + 11 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) →
    (0.5 + 11 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) →
    (0.5 + 11 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (¬(0.5 + 11 ^ (-335 : ℤ) ≤ landauConstant)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (¬(0.5 + 11 ^ (-335 : ℤ) ≤ landauConstant)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) ↔ (0.5 + 11 ^ (-335 : ℤ) ≤ landauConstant)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) ↔ (0.5 + 11 ^ (-335 : ℤ) ≤ landauConstant)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant

set_option maxHeartbeats 200000 in
example : Prop :=
  0.5 + 10 ^ (-335 : ℤ) ≥ landauConstant

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) ≥ landauConstant) →
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) ≥ landauConstant) →
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) ≥ landauConstant) →
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) ≥ landauConstant) →
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) ≥ landauConstant) →
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) ≥ landauConstant) →
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) ≥ landauConstant) →
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) →
    (0.5 + 10 ^ (-335 : ℤ) ≥ landauConstant) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) →
    (0.5 + 10 ^ (-335 : ℤ) ≥ landauConstant) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) →
    (0.5 + 10 ^ (-335 : ℤ) ≥ landauConstant) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) →
    (0.5 + 10 ^ (-335 : ℤ) ≥ landauConstant) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) →
    (0.5 + 10 ^ (-335 : ℤ) ≥ landauConstant) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) →
    (0.5 + 10 ^ (-335 : ℤ) ≥ landauConstant) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) →
    (0.5 + 10 ^ (-335 : ℤ) ≥ landauConstant) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (¬(0.5 + 10 ^ (-335 : ℤ) ≥ landauConstant)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (¬(0.5 + 10 ^ (-335 : ℤ) ≥ landauConstant)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) ↔ (0.5 + 10 ^ (-335 : ℤ) ≥ landauConstant)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) ↔ (0.5 + 10 ^ (-335 : ℤ) ≥ landauConstant)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant

set_option maxHeartbeats 200000 in
example : Prop :=
  landauConstant ≥ 0.5 + 10 ^ (-335 : ℤ)

set_option maxHeartbeats 200000 in
example  :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) ↔ (landauConstant ≥ 0.5 + 10 ^ (-335 : ℤ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example  :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) ↔ (landauConstant ≥ 0.5 + 10 ^ (-335 : ℤ)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example  :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) ↔ (landauConstant ≥ 0.5 + 10 ^ (-335 : ℤ)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example  :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) ↔ (landauConstant ≥ 0.5 + 10 ^ (-335 : ℤ)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example  :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) ↔ (landauConstant ≥ 0.5 + 10 ^ (-335 : ℤ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example  :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) ↔ (landauConstant ≥ 0.5 + 10 ^ (-335 : ℤ)) := by
  omega

set_option maxHeartbeats 200000 in
example  :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) ↔ (landauConstant ≥ 0.5 + 10 ^ (-335 : ℤ)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example  :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) ↔ (landauConstant ≥ 0.5 + 10 ^ (-335 : ℤ)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) ↔
    (landauConstant ≥ 0.5 + 10 ^ (-335 : ℤ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) ↔
    (landauConstant ≥ 0.5 + 10 ^ (-335 : ℤ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) ↔
    (landauConstant ≥ 0.5 + 10 ^ (-335 : ℤ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) ↔
    (landauConstant ≥ 0.5 + 10 ^ (-335 : ℤ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant

set_option maxHeartbeats 200000 in
example : Prop :=
  ¬(landauConstant < 0.5 + 10 ^ (-335 : ℤ))

set_option maxHeartbeats 200000 in
example  :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) ↔ (¬(landauConstant < 0.5 + 10 ^ (-335 : ℤ))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example  :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) ↔ (¬(landauConstant < 0.5 + 10 ^ (-335 : ℤ))) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example  :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) ↔ (¬(landauConstant < 0.5 + 10 ^ (-335 : ℤ))) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example  :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) ↔ (¬(landauConstant < 0.5 + 10 ^ (-335 : ℤ))) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example  :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) ↔ (¬(landauConstant < 0.5 + 10 ^ (-335 : ℤ))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example  :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) ↔ (¬(landauConstant < 0.5 + 10 ^ (-335 : ℤ))) := by
  omega

set_option maxHeartbeats 200000 in
example  :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) ↔ (¬(landauConstant < 0.5 + 10 ^ (-335 : ℤ))) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example  :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) ↔ (¬(landauConstant < 0.5 + 10 ^ (-335 : ℤ))) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) ↔
    (¬(landauConstant < 0.5 + 10 ^ (-335 : ℤ))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) ↔
    (¬(landauConstant < 0.5 + 10 ^ (-335 : ℤ))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) ↔
    (¬(landauConstant < 0.5 + 10 ^ (-335 : ℤ))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) ↔
    (¬(landauConstant < 0.5 + 10 ^ (-335 : ℤ))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant

set_option maxHeartbeats 200000 in
example : Prop :=
  landauConstant > 0.5 + 10 ^ (-335 : ℤ)

set_option maxHeartbeats 200000 in
example :
    (landauConstant > 0.5 + 10 ^ (-335 : ℤ)) →
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (landauConstant > 0.5 + 10 ^ (-335 : ℤ)) →
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (landauConstant > 0.5 + 10 ^ (-335 : ℤ)) →
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (landauConstant > 0.5 + 10 ^ (-335 : ℤ)) →
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (landauConstant > 0.5 + 10 ^ (-335 : ℤ)) →
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (landauConstant > 0.5 + 10 ^ (-335 : ℤ)) →
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (landauConstant > 0.5 + 10 ^ (-335 : ℤ)) →
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (¬(landauConstant > 0.5 + 10 ^ (-335 : ℤ))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (¬(landauConstant > 0.5 + 10 ^ (-335 : ℤ))) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) ↔ (landauConstant > 0.5 + 10 ^ (-335 : ℤ))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) ↔ (landauConstant > 0.5 + 10 ^ (-335 : ℤ))) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant

set_option maxHeartbeats 200000 in
example : Prop :=
  landauConstant ≥ 0.5 + 11 ^ (-335 : ℤ)

set_option maxHeartbeats 200000 in
example :
    (landauConstant ≥ 0.5 + 11 ^ (-335 : ℤ)) →
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (landauConstant ≥ 0.5 + 11 ^ (-335 : ℤ)) →
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (landauConstant ≥ 0.5 + 11 ^ (-335 : ℤ)) →
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (landauConstant ≥ 0.5 + 11 ^ (-335 : ℤ)) →
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (landauConstant ≥ 0.5 + 11 ^ (-335 : ℤ)) →
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (landauConstant ≥ 0.5 + 11 ^ (-335 : ℤ)) →
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (landauConstant ≥ 0.5 + 11 ^ (-335 : ℤ)) →
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) →
    (landauConstant ≥ 0.5 + 11 ^ (-335 : ℤ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) →
    (landauConstant ≥ 0.5 + 11 ^ (-335 : ℤ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) →
    (landauConstant ≥ 0.5 + 11 ^ (-335 : ℤ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) →
    (landauConstant ≥ 0.5 + 11 ^ (-335 : ℤ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) →
    (landauConstant ≥ 0.5 + 11 ^ (-335 : ℤ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) →
    (landauConstant ≥ 0.5 + 11 ^ (-335 : ℤ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) →
    (landauConstant ≥ 0.5 + 11 ^ (-335 : ℤ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (¬(landauConstant ≥ 0.5 + 11 ^ (-335 : ℤ))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (¬(landauConstant ≥ 0.5 + 11 ^ (-335 : ℤ))) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) ↔ (landauConstant ≥ 0.5 + 11 ^ (-335 : ℤ))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) ↔ (landauConstant ≥ 0.5 + 11 ^ (-335 : ℤ))) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant

set_option maxHeartbeats 200000 in
example : Prop :=
  landauConstant ≤ 0.5 + 10 ^ (-335 : ℤ)

set_option maxHeartbeats 200000 in
example :
    (landauConstant ≤ 0.5 + 10 ^ (-335 : ℤ)) →
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (landauConstant ≤ 0.5 + 10 ^ (-335 : ℤ)) →
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (landauConstant ≤ 0.5 + 10 ^ (-335 : ℤ)) →
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (landauConstant ≤ 0.5 + 10 ^ (-335 : ℤ)) →
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (landauConstant ≤ 0.5 + 10 ^ (-335 : ℤ)) →
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (landauConstant ≤ 0.5 + 10 ^ (-335 : ℤ)) →
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (landauConstant ≤ 0.5 + 10 ^ (-335 : ℤ)) →
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) →
    (landauConstant ≤ 0.5 + 10 ^ (-335 : ℤ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) →
    (landauConstant ≤ 0.5 + 10 ^ (-335 : ℤ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) →
    (landauConstant ≤ 0.5 + 10 ^ (-335 : ℤ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) →
    (landauConstant ≤ 0.5 + 10 ^ (-335 : ℤ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) →
    (landauConstant ≤ 0.5 + 10 ^ (-335 : ℤ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) →
    (landauConstant ≤ 0.5 + 10 ^ (-335 : ℤ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) →
    (landauConstant ≤ 0.5 + 10 ^ (-335 : ℤ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (¬(landauConstant ≤ 0.5 + 10 ^ (-335 : ℤ))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (¬(landauConstant ≤ 0.5 + 10 ^ (-335 : ℤ))) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) ↔ (landauConstant ≤ 0.5 + 10 ^ (-335 : ℤ))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant) ↔ (landauConstant ≤ 0.5 + 10 ^ (-335 : ℤ))) :=
  by decide

#eval "FIN_CERTIFICAR"
